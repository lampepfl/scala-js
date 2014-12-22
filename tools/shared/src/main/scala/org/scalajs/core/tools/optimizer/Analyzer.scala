/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js tools             **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013-2014, LAMP/EPFL   **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package org.scalajs.core.tools.optimizer

import scala.annotation.tailrec

import scala.collection.mutable

import org.scalajs.core.ir
import ir.{ClassKind, Definitions, Infos}
import Definitions.{isConstructorName, isReflProxyName}

import org.scalajs.core.tools.sem._
import org.scalajs.core.tools.javascript.LongImpl

import ScalaJSOptimizer._

final class Analyzer(semantics: Semantics,
    reachOptimizerSymbols: Boolean) extends Analysis {
  import Analyzer._
  import Analysis._

  private[this] var _allAvailable: Boolean = true
  private[this] val _classInfos = mutable.Map.empty[String, ClassInfo]
  private[this] val _errors = mutable.Buffer.empty[Error]

  def allAvailable: Boolean = _allAvailable
  def classInfos: scala.collection.Map[String, Analysis.ClassInfo] = _classInfos
  def errors: Seq[Error] = _errors

  private def lookupClass(encodedName: String): ClassInfo = {
    _classInfos.get(encodedName) match {
      case Some(info) => info
      case None =>
        val c = new ClassInfo(createMissingClassInfo(encodedName))
        _classInfos += encodedName -> c
        c.nonExistent = true
        c.linkClasses()
        c
    }
  }

  def computeReachability(allData: Seq[Infos.ClassInfo]): Analysis = {
    require(_classInfos.isEmpty, "Cannot run the same Analyzer multiple times")

    // Load data
    for (classData <- allData)
      _classInfos += classData.encodedName -> new ClassInfo(classData)

    linkClasses()

    reachCoreSymbols()

    // Reach all user stuff
    for (classInfo <- _classInfos.values)
      classInfo.reachExports()

    this
  }

  private def linkClasses(): Unit = {
    if (!_classInfos.contains(ir.Definitions.ObjectClass))
      sys.error("Fatal error: could not find java.lang.Object on the classpath")
    for (classInfo <- _classInfos.values.toList)
      classInfo.linkClasses()
  }

  /** Reach symbols used directly by scalajsenv.js. */
  private def reachCoreSymbols(): Unit = {
    import semantics._
    import CheckedBehavior._

    implicit val from = FromCore

    def instantiateClassWith(className: String, constructor: String): ClassInfo = {
      val info = lookupClass(className)
      info.instantiated()
      info.callMethod(constructor)
      info
    }

    val ObjectClass = instantiateClassWith("O", "init___")
    ObjectClass.callMethod("toString__T")
    ObjectClass.callMethod("equals__O__Z")

    instantiateClassWith("jl_NullPointerException", "init___")

    if (asInstanceOfs != Unchecked)
      instantiateClassWith("jl_ClassCastException", "init___T")

    if (asInstanceOfs == Fatal)
      instantiateClassWith("sjsr_UndefinedBehaviorError", "init___jl_Throwable")

    instantiateClassWith("jl_Class", "init___jl_ScalaJSClassData")

    val DoubleModuleClass = lookupClass("jl_Double$")
    DoubleModuleClass.accessModule()
    DoubleModuleClass.callMethod("compare__D__D__I")

    val RTStringModuleClass = lookupClass("sjsr_RuntimeString$")
    RTStringModuleClass.accessModule()
    RTStringModuleClass.callMethod("hashCode__T__I")

    val RTLongClass = lookupClass(LongImpl.RuntimeLongClass)
    RTLongClass.instantiated()
    for (method <- LongImpl.AllConstructors ++ LongImpl.AllMethods)
      RTLongClass.callMethod(method)

    if (reachOptimizerSymbols) {
      for (method <- LongImpl.AllIntrinsicMethods)
        RTLongClass.callMethod(method)
    }

    val RTLongModuleClass = lookupClass(LongImpl.RuntimeLongModuleClass)
    RTLongModuleClass.accessModule()
    for (method <- LongImpl.AllModuleMethods)
      RTLongModuleClass.callMethod(method)

    if (reachOptimizerSymbols) {
      for (hijacked <- Definitions.HijackedClasses)
        lookupClass(hijacked).instantiated()
    } else {
      for (hijacked <- Definitions.HijackedClasses)
        lookupClass(hijacked).accessData()
    }

    if (semantics.strictFloats) {
      val RuntimePackage = lookupClass("sjsr_package$")
      RuntimePackage.accessModule()
      RuntimePackage.callMethod("froundPolyfill__D__D")
    }

    val BitsModuleClass = lookupClass("sjsr_Bits$")
    BitsModuleClass.accessModule()
    BitsModuleClass.callMethod("numberHashCode__D__I")
  }

  private class ClassInfo(data: Infos.ClassInfo) extends Analysis.ClassInfo {
    private[this] var _linking = false
    private[this] var _linked = false

    val encodedName = data.encodedName
    val kind = data.kind
    val isStaticModule = data.kind == ClassKind.ModuleClass
    val isInterface = data.kind == ClassKind.Interface
    val isRawJSType = data.kind == ClassKind.RawJSType
    val isHijackedClass = data.kind == ClassKind.HijackedClass
    val isClass = !isInterface && !isRawJSType
    val isExported = data.isExported

    var superClass: ClassInfo = _
    var ancestors: List[ClassInfo] = _
    val descendants = mutable.ListBuffer.empty[ClassInfo]

    var nonExistent: Boolean = false

    /** Ensures that this class and its dependencies are linked.
     *
     *  @throws CyclicDependencyException if this class is already linking
     */
    def linkClasses(): Unit = {
      if (_linking)
        throw CyclicDependencyException(encodedName :: Nil)

      if (!_linked) {
        _linking = true
        try {
          linkClassesImpl()
        } catch {
          case CyclicDependencyException(chain) =>
            throw CyclicDependencyException(encodedName :: chain)
        }
        _linking = false
        _linked = true
      }
    }

    private[this] def linkClassesImpl(): Unit = {
      if (data.superClass != "")
        superClass = lookupClass(data.superClass)

      ancestors = this +: data.parents.flatMap { anc =>
        val cls = lookupClass(anc)
        cls.linkClasses()
        cls.ancestors
      }.distinct

      for (ancestor <- ancestors)
        ancestor.descendants += this
    }

    lazy val ancestorCount: Int =
      if (superClass == null) 0
      else superClass.ancestorCount + 1

    lazy val descendentClasses = descendants.filter(_.isClass)

    var isInstantiated: Boolean = false
    var isAnySubclassInstantiated: Boolean = false
    var isModuleAccessed: Boolean = false
    var isDataAccessed: Boolean = false

    var instantiatedFrom: Option[From] = None

    val delayedCalls = mutable.Map.empty[String, From]

    def isNeededAtAll =
      isDataAccessed ||
      isAnySubclassInstantiated ||
      isAnyStaticMethodReachable

    def isAnyStaticMethodReachable =
      staticMethodInfos.values.exists(_.isReachable)

    lazy val (methodInfos, staticMethodInfos) = {
      val allInfos = for (methodData <- data.methods)
        yield (methodData.encodedName, new MethodInfo(this, methodData))
      val (staticMethodInfos, methodInfos) = allInfos.partition(_._2.isStatic)
      (mutable.Map(methodInfos: _*), mutable.Map(staticMethodInfos: _*))
    }

    def lookupMethod(methodName: String): MethodInfo = {
      tryLookupMethod(methodName).getOrElse {
        val syntheticData = createMissingMethodInfo(methodName)
        val m = new MethodInfo(this, syntheticData)
        m.nonExistent = true
        methodInfos += methodName -> m
        m
      }
    }

    def tryLookupMethod(methodName: String): Option[MethodInfo] = {
      assert(isClass,
          s"Cannot call lookupMethod($methodName) on non-class $this")
      @tailrec
      def loop(ancestorInfo: ClassInfo): Option[MethodInfo] = {
        if (ancestorInfo ne null) {
          ancestorInfo.methodInfos.get(methodName) match {
            case Some(m) if !m.isAbstract => Some(m)
            case _ => loop(ancestorInfo.superClass)
          }
        } else {
          None
        }
      }
      loop(this)
    }

    def lookupStaticMethod(methodName: String): MethodInfo = {
      tryLookupStaticMethod(methodName).getOrElse {
        val syntheticData = createMissingMethodInfo(methodName, isStatic = true)
        val m = new MethodInfo(this, syntheticData)
        m.nonExistent = true
        staticMethodInfos += methodName -> m
        m
      }
    }

    def tryLookupStaticMethod(methodName: String): Option[MethodInfo] =
      staticMethodInfos.get(methodName)

    override def toString(): String = encodedName

    /** Start reachability algorithm with the exports for that class. */
    def reachExports(): Unit = {
      implicit val from = FromExports

      // Myself
      if (isExported) {
        if (isStaticModule) accessModule()
        else instantiated()
      }

      // My methods
      for (methodInfo <- methodInfos.values) {
        if (methodInfo.isExported)
          callMethod(methodInfo.encodedName)
      }
    }

    def accessModule()(implicit from: From): Unit = {
      if (!isStaticModule) {
        _errors += NotAModule(this, from)
      } else if (!isModuleAccessed) {
        isModuleAccessed = true
        instantiated()
        callMethod("init___")
      }
    }

    def instantiated()(implicit from: From): Unit = {
      if (!isInstantiated && isClass) {
        isInstantiated = true
        instantiatedFrom = Some(from)
        ancestors.foreach(_.subclassInstantiated())

        for ((methodName, from) <- delayedCalls)
          delayedCallMethod(methodName)(from)
      }
    }

    private def subclassInstantiated()(implicit from: From): Unit = {
      if (!isAnySubclassInstantiated && isClass) {
        isAnySubclassInstantiated = true
        if (instantiatedFrom.isEmpty)
          instantiatedFrom = Some(from)
        accessData()
      }
    }

    def accessData()(implicit from: From): Unit = {
      if (!isDataAccessed) {
        checkExistent()
        isDataAccessed = true
      }
    }

    def checkExistent()(implicit from: From): Unit = {
      if (nonExistent) {
        _errors += MissingClass(this, from)
        nonExistent = false
        _allAvailable = false
      }
    }

    def callMethod(methodName: String, statically: Boolean = false)(
        implicit from: From): Unit = {
      if (isConstructorName(methodName)) {
        // constructors are always implicitly called statically
        lookupMethod(methodName).reachStatic()
      } else if (statically) {
        assert(!isReflProxyName(methodName),
            s"Trying to call statically refl proxy $this.$methodName")
        lookupMethod(methodName).reachStatic()
      } else {
        for (descendentClass <- descendentClasses) {
          if (descendentClass.isInstantiated)
            descendentClass.delayedCallMethod(methodName)
          else
            descendentClass.delayedCalls += ((methodName, from))
        }
      }
    }

    private def delayedCallMethod(methodName: String)(implicit from: From): Unit = {
      if (isReflProxyName(methodName)) {
        tryLookupMethod(methodName).foreach(_.reach(this))
      } else {
        lookupMethod(methodName).reach(this)
      }
    }

    def callStaticMethod(methodName: String)(implicit from: From): Unit = {
      lookupStaticMethod(methodName).reachStatic()
    }
  }

  private class MethodInfo(val owner: ClassInfo,
      data: Infos.MethodInfo) extends Analysis.MethodInfo {

    val encodedName = data.encodedName
    val isStatic = data.isStatic
    val isAbstract = data.isAbstract
    val isExported = data.isExported
    val isReflProxy = isReflProxyName(encodedName)

    var isReachable: Boolean = false

    var calledFrom: Option[From] = None
    var instantiatedSubclass: Option[ClassInfo] = None

    var nonExistent: Boolean = false

    override def toString(): String = s"$owner.$encodedName"

    def reachStatic()(implicit from: From): Unit = {
      assert(!isAbstract,
          s"Trying to reach statically the abstract method $this")

      checkExistent()

      if (!isReachable) {
        isReachable = true
        calledFrom = Some(from)
        doReach()
      }
    }

    def reach(inClass: ClassInfo)(implicit from: From): Unit = {
      assert(!isStatic,
          s"Trying to dynamically reach the static method $this")
      assert(!isAbstract,
          s"Trying to dynamically reach the abstract method $this")
      assert(owner.isClass,
          s"Trying to dynamically reach the non-class method $this")
      assert(!isConstructorName(encodedName),
          s"Trying to dynamically reach the constructor $this")

      checkExistent()

      if (!isReachable) {
        isReachable = true
        calledFrom = Some(from)
        instantiatedSubclass = Some(inClass)
        doReach()
      }
    }

    private def checkExistent()(implicit from: From) = {
      if (nonExistent) {
        _errors += MissingMethod(this, from)
        _allAvailable = false
      }
    }

    private[this] def doReach(): Unit = {
      implicit val from = FromMethod(this)

      for (moduleName <- data.accessedModules) {
        lookupClass(moduleName).accessModule()
      }

      for (className <- data.instantiatedClasses) {
        lookupClass(className).instantiated()
      }

      for (className <- data.accessedClassData) {
        lookupClass(className).accessData()
      }

      for ((className, methods) <- data.methodsCalled) {
        val classInfo = lookupClass(className)
        for (methodName <- methods)
          classInfo.callMethod(methodName)
      }

      for ((className, methods) <- data.methodsCalledStatically) {
        val classInfo = lookupClass(className)
        for (methodName <- methods)
          classInfo.callMethod(methodName, statically = true)
      }

      for ((className, methods) <- data.staticMethodsCalled) {
        val classInfo = lookupClass(className)
        for (methodName <- methods)
          classInfo.callStaticMethod(methodName)
      }
    }
  }

  private def createMissingClassInfo(encodedName: String): Infos.ClassInfo = {
    // We create a module class to avoid cascading errors
    Infos.ClassInfo(
        encodedName = encodedName,
        isExported = false,
        kind = ClassKind.ModuleClass,
        superClass = "O",
        parents = List("O"),
        methods = List(
            createMissingMethodInfo("init___"))
    )
  }

  private def createMissingMethodInfo(encodedName: String,
      isStatic: Boolean = false,
      isAbstract: Boolean = false): Infos.MethodInfo = {
    Infos.MethodInfo(encodedName = encodedName,
        isStatic = isStatic, isAbstract = isAbstract)
  }

}

object Analyzer {

  final case class CyclicDependencyException(
      chain: List[String]) extends Exception(mkMsg(chain))

  private def mkMsg(chain: List[String]) = {
    val buf = new StringBuffer
    buf.append("A cyclic dependency has been encountered: \n")
    for (elem <- chain)
      buf.append(s"  - $elem\n")
    buf.toString
  }
}
