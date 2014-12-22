/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js tools             **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013-2014, LAMP/EPFL   **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package org.scalajs.core.tools.optimizer

import language.higherKinds

import scala.annotation.{switch, tailrec}

import scala.collection.{GenMap, GenTraversableOnce, GenIterable, GenIterableLike}
import scala.collection.mutable

import org.scalajs.core.ir._
import Definitions.isConstructorName
import Trees._
import Types._

import org.scalajs.core.tools.sem._

import org.scalajs.core.tools.javascript
import javascript.Trees.{Tree => JSTree}
import javascript.ScalaJSClassEmitter

import org.scalajs.core.tools.logging._

/** Incremental optimizer.
 *  An incremental optimizer consumes the reachability [[Analysis]] produced by
 *  an [[Analyzer]], as well as trees for classes, and optimizes them in an
 *  incremental way.
 *  It maintains state between runs to do a minimal amount of work on every
 *  run, based on detecting what parts of the program must be re-optimized,
 *  and keeping optimized results from previous runs for the rest.
 */
abstract class GenIncOptimizer(semantics: Semantics) {
  import GenIncOptimizer._

  protected val CollOps: AbsCollOps

  private val classEmitter = new ScalaJSClassEmitter(semantics)

  private var logger: Logger = _

  /** Are we in batch mode? I.e., are we running from scratch?
   *  Various parts of the algorithm can be skipped entirely when running in
   *  batch mode.
   */
  private var batchMode: Boolean = false

  /** Should positions be considered when comparing tree hashes */
  private var considerPositions: Boolean = _

  private var objectClass: Class = _
  private val classes = CollOps.emptyMap[String, Class]
  private val statics = CollOps.emptyParMap[String, StaticsNamespace]

  protected def getInterface(encodedName: String): InterfaceType

  /** Schedule a method for processing in the PROCESS PASS */
  protected def scheduleMethod(method: MethodImpl): Unit

  protected def newMethodImpl(owner: MethodContainer,
      encodedName: String): MethodImpl

  def findStaticsNamespace(encodedName: String): StaticsNamespace =
    statics(encodedName)
  def findClass(encodedName: String): Class =
    classes(encodedName)

  def getStaticsNamespace(encodedName: String): Option[StaticsNamespace] =
    statics.get(encodedName)
  def getClass(encodedName: String): Option[Class] =
    classes.get(encodedName)

  type GetClassTreeIfChanged =
    (String, Option[String]) => Option[(ClassDef, Option[String])]

  private def withLogger[A](logger: Logger)(body: => A): A = {
    assert(this.logger == null)
    this.logger = logger
    try body
    finally this.logger = null
  }

  /** Update the incremental analyzer with a new run. */
  def update(analysis: Analysis,
      getClassTreeIfChanged: GetClassTreeIfChanged, considerPositions: Boolean,
      logger: Logger): Unit = withLogger(logger) {

    batchMode = objectClass == null
    this.considerPositions = considerPositions
    logger.debug(s"Optimizer batch mode: $batchMode")

    logTime(logger, "Incremental part of inc. optimizer") {
      /* UPDATE PASS */
      updateAndTagEverything(analysis, getClassTreeIfChanged)
    }

    logTime(logger, "Optimizer part of inc. optimizer") {
      /* PROCESS PASS */
      processAllTaggedMethods()
    }
  }

  /** Incremental part: update state and detect what needs to be re-optimized.
   *  UPDATE PASS ONLY. (This IS the update pass).
   */
  private def updateAndTagEverything(analysis: Analysis,
      getClassTreeIfChanged: GetClassTreeIfChanged): Unit = {

    val neededClasses = CollOps.emptyParMap[String, Analysis.ClassInfo]
    val neededStatics = CollOps.emptyParMap[String, Analysis.ClassInfo]
    for {
      classInfo <- analysis.classInfos.values
      if classInfo.isNeededAtAll
    } {
      if (classInfo.isAnySubclassInstantiated && !(
          classInfo.kind == ClassKind.Interface ||
          classInfo.kind == ClassKind.RawJSType))
        CollOps.put(neededClasses, classInfo.encodedName, classInfo)
      if (classInfo.isAnyStaticMethodReachable)
        CollOps.put(neededStatics, classInfo.encodedName, classInfo)
    }

    /* Remove deleted statics, and update existing statics.
     * We don't even have to notify callers in case of additions or removals
     * because callers have got to be invalidated by themselves.
     * Only changed methods need to trigger notifications.
     *
     * Non-batch mode only.
     */
    assert(!batchMode || statics.isEmpty)
    if (!batchMode) {
      CollOps.retain(statics) { (staticsName, staticsNS) =>
        CollOps.remove(neededStatics, staticsName).fold {
          /* Deleted trait impl. Mark all its methods as deleted, and remove it
           * from known trait impls.
           */
          staticsNS.methods.values.foreach(_.delete())

          false
        } { traitImplInfo =>
          /* Existing trait impl. Update it. */
          val (added, changed, removed) =
            staticsNS.updateWith(traitImplInfo, getClassTreeIfChanged)
          for (method <- changed)
            staticsNS.myInterface.tagStaticCallersOf(method)

          true
        }
      }
    }

    /* Add new statics.
     * Easy, we don't have to notify anyone.
     */
    for (classInfo <- neededStatics.values) {
      val staticsNS = new StaticsNamespace(classInfo.encodedName)
      CollOps.put(statics, staticsNS.encodedName, staticsNS)
      staticsNS.updateWith(classInfo, getClassTreeIfChanged)
    }

    if (!batchMode) {
      /* Class removals:
       * * If a class is deleted or moved, delete its entire subtree (because
       *   all its descendants must also be deleted or moved).
       * * If an existing class was instantiated but is no more, notify callers
       *   of its methods.
       *
       * Non-batch mode only.
       */
      val objectClassStillExists =
        objectClass.walkClassesForDeletions(neededClasses.get(_))
      assert(objectClassStillExists, "Uh oh, java.lang.Object was deleted!")

      /* Class changes:
       * * Delete removed methods, update existing ones, add new ones
       * * Update the list of ancestors
       * * Class newly instantiated
       *
       * Non-batch mode only.
       */
      objectClass.walkForChanges(
          CollOps.remove(neededClasses, _).get,
          getClassTreeIfChanged,
          Set.empty)
    }

    /* Class additions:
     * * Add new classes (including those that have moved from elsewhere).
     * In batch mode, we avoid doing notifications.
     */

    // Group children by (immediate) parent
    val newChildrenByParent = CollOps.emptyAccMap[String, Analysis.ClassInfo]

    for (classInfo <- neededClasses.values) {
      val superInfo = classInfo.superClass
      if (superInfo == null) {
        assert(batchMode, "Trying to add java.lang.Object in incremental mode")
        objectClass = new Class(None, classInfo.encodedName)
        classes += classInfo.encodedName -> objectClass
        objectClass.setupAfterCreation(classInfo, getClassTreeIfChanged)
      } else {
        CollOps.acc(newChildrenByParent, superInfo.encodedName, classInfo)
      }
    }

    val getNewChildren =
      (name: String) => CollOps.getAcc(newChildrenByParent, name)

    // Walk the tree to add children
    if (batchMode) {
      objectClass.walkForAdditions(getNewChildren, getClassTreeIfChanged)
    } else {
      val existingParents =
        CollOps.parFlatMapKeys(newChildrenByParent)(classes.get)
      for (parent <- existingParents)
        parent.walkForAdditions(getNewChildren, getClassTreeIfChanged)
    }

  }

  /** Optimizer part: process all methods that need reoptimizing.
   *  PROCESS PASS ONLY. (This IS the process pass).
   */
  protected def processAllTaggedMethods(): Unit

  protected def logProcessingMethods(count: Int): Unit =
    logger.debug(s"Optimizing $count methods.")

  /** Base class for [[Class]] and [[TraitImpl]]. */
  abstract class MethodContainer(val encodedName: String,
      val isStatic: Boolean) {
    def thisType: Type

    val myInterface = getInterface(encodedName)

    val methods = mutable.Map.empty[String, MethodImpl]

    var lastVersion: Option[String] = None

    protected var optimizerHints: OptimizerHints = OptimizerHints.empty

    private def reachableMethodsOf(info: Analysis.ClassInfo): Set[String] = {
      val methodInfos: scala.collection.Map[String, Analysis.MethodInfo] =
        if (isStatic) info.staticMethodInfos
        else info.methodInfos
      (for {
        methodInfo <- methodInfos.values
        if methodInfo.isReachable && !methodInfo.isAbstract
      } yield {
        methodInfo.encodedName
      }).toSet
    }

    /** UPDATE PASS ONLY. Global concurrency safe but not on same instance */
    def updateWith(info: Analysis.ClassInfo,
        getClassTreeIfChanged: GetClassTreeIfChanged): (Set[String], Set[String], Set[String]) = {
      if (!isStatic)
        myInterface.ancestors = info.ancestors.map(_.encodedName).toList

      val addedMethods = Set.newBuilder[String]
      val changedMethods = Set.newBuilder[String]
      val deletedMethods = Set.newBuilder[String]

      val reachableMethods = reachableMethodsOf(info)
      val methodSetChanged = methods.keySet != reachableMethods
      if (methodSetChanged) {
        // Remove deleted methods
        methods retain { (methodName, method) =>
          if (reachableMethods.contains(methodName)) {
            true
          } else {
            deletedMethods += methodName
            method.delete()
            false
          }
        }
        // Clear lastVersion if there are new methods
        if (reachableMethods.exists(!methods.contains(_)))
          lastVersion = None
      }
      for ((tree, version) <- getClassTreeIfChanged(encodedName, lastVersion)) {
        lastVersion = version
        this match {
          case cls: Class =>
            cls.isModuleClass = tree.kind == ClassKind.ModuleClass
            cls.fields = for (field @ VarDef(_, _, _, _) <- tree.defs) yield field
          case _          =>
        }
        tree.defs.foreach {
          case methodDef: MethodDef if methodDef.name.isInstanceOf[Ident] &&
              reachableMethods.contains(methodDef.name.name) &&
              methodDef.static == isStatic =>
            val methodName = methodDef.name.name

            val methodInfo =
              if (isStatic) info.staticMethodInfos(methodName)
              else info.methodInfos(methodName)

            methods.get(methodName).fold {
              addedMethods += methodName
              val method = newMethodImpl(this, methodName)
              method.updateWith(methodInfo, methodDef)
              methods(methodName) = method
              method
            } { method =>
              if (method.updateWith(methodInfo, methodDef))
                changedMethods += methodName
              method
            }

          case _ => // ignore
        }
        optimizerHints = tree.optimizerHints
      }

      (addedMethods.result(), changedMethods.result(), deletedMethods.result())
    }
  }

  /** Class in the class hierarchy (not an interface).
   *  A class may be a module class.
   *  A class knows its superclass and the interfaces it implements. It also
   *  maintains a list of its direct subclasses, so that the instances of
   *  [[Class]] form a tree of the class hierarchy.
   */
  class Class(val superClass: Option[Class],
      _encodedName: String) extends MethodContainer(
      _encodedName, isStatic = false) {
    if (encodedName == Definitions.ObjectClass) {
      assert(superClass.isEmpty)
      assert(objectClass == null)
    } else {
      assert(superClass.isDefined)
    }

    /** Parent chain from this to Object. */
    val parentChain: List[Class] =
      this :: superClass.fold[List[Class]](Nil)(_.parentChain)

    /** Reverse parent chain from Object to this. */
    val reverseParentChain: List[Class] =
      parentChain.reverse

    def thisType: Type = ClassType(encodedName)

    var interfaces: Set[InterfaceType] = Set.empty
    var subclasses: CollOps.ParIterable[Class] = CollOps.emptyParIterable
    var isInstantiated: Boolean = false

    var isModuleClass: Boolean = false
    var hasElidableModuleAccessor: Boolean = false

    var fields: List[VarDef] = Nil
    var isInlineable: Boolean = false
    var tryNewInlineable: Option[RecordValue] = None

    override def toString(): String =
      encodedName

    /** Walk the class hierarchy tree for deletions.
     *  This includes "deleting" classes that were previously instantiated but
     *  are no more.
     *  UPDATE PASS ONLY. Not concurrency safe on same instance.
     */
    def walkClassesForDeletions(
        getClassInfoIfNeeded: String => Option[Analysis.ClassInfo]): Boolean = {
      def sameSuperClass(info: Analysis.ClassInfo): Boolean =
        if (info.superClass == null) superClass.isEmpty
        else superClass.exists(_.encodedName == info.superClass.encodedName)

      getClassInfoIfNeeded(encodedName) match {
        case Some(classInfo) if sameSuperClass(classInfo) =>
          // Class still exists. Recurse.
          subclasses = subclasses.filter(
              _.walkClassesForDeletions(getClassInfoIfNeeded))
          if (isInstantiated && !classInfo.isInstantiated)
            notInstantiatedAnymore()
          true
        case _ =>
          // Class does not exist or has been moved. Delete the entire subtree.
          deleteSubtree()
          false
      }
    }

    /** Delete this class and all its subclasses. UPDATE PASS ONLY. */
    def deleteSubtree(): Unit = {
      delete()
      for (subclass <- subclasses)
        subclass.deleteSubtree()
    }

    /** UPDATE PASS ONLY. */
    private def delete(): Unit = {
      if (isInstantiated)
        notInstantiatedAnymore()
      for (method <- methods.values)
        method.delete()
      classes -= encodedName
      /* Note: no need to tag methods that call *statically* one of the methods
       * of the deleted classes, since they've got to be invalidated by
       * themselves.
       */
    }

    /** UPDATE PASS ONLY. */
    def notInstantiatedAnymore(): Unit = {
      assert(isInstantiated)
      isInstantiated = false
      for (intf <- interfaces) {
        intf.removeInstantiatedSubclass(this)
        for (methodName <- allMethods().keys)
          intf.tagDynamicCallersOf(methodName)
      }
    }

    /** UPDATE PASS ONLY. */
    def walkForChanges(
        getClassInfo: String => Analysis.ClassInfo,
        getClassTreeIfChanged: GetClassTreeIfChanged,
        parentMethodAttributeChanges: Set[String]): Unit = {

      val classInfo = getClassInfo(encodedName)

      val (addedMethods, changedMethods, deletedMethods) =
        updateWith(classInfo, getClassTreeIfChanged)

      val oldInterfaces = interfaces
      val newInterfaces =
        classInfo.ancestors.map(info => getInterface(info.encodedName)).toSet
      interfaces = newInterfaces

      val methodAttributeChanges =
        (parentMethodAttributeChanges -- methods.keys ++
            addedMethods ++ changedMethods ++ deletedMethods)

      // Tag callers with dynamic calls
      val wasInstantiated = isInstantiated
      isInstantiated = classInfo.isInstantiated
      assert(!(wasInstantiated && !isInstantiated),
          "(wasInstantiated && !isInstantiated) should have been handled "+
          "during deletion phase")

      if (isInstantiated) {
        if (wasInstantiated) {
          val existingInterfaces = oldInterfaces.intersect(newInterfaces)
          for {
            intf <- existingInterfaces
            methodName <- methodAttributeChanges
          } {
            intf.tagDynamicCallersOf(methodName)
          }
          if (newInterfaces.size != oldInterfaces.size ||
              newInterfaces.size != existingInterfaces.size) {
            val allMethodNames = allMethods().keys
            for {
              intf <- oldInterfaces ++ newInterfaces -- existingInterfaces
              methodName <- allMethodNames
            } {
              intf.tagDynamicCallersOf(methodName)
            }
          }
        } else {
          val allMethodNames = allMethods().keys
          for (intf <- interfaces) {
            intf.addInstantiatedSubclass(this)
            for (methodName <- allMethodNames)
              intf.tagDynamicCallersOf(methodName)
          }
        }
      }

      // Tag callers with static calls
      for (methodName <- methodAttributeChanges)
        myInterface.tagStaticCallersOf(methodName)

      // Module class specifics
      updateHasElidableModuleAccessor()

      // Inlineable class
      if (updateIsInlineable(classInfo)) {
        for (method <- methods.values; if isConstructorName(method.encodedName))
          myInterface.tagStaticCallersOf(method.encodedName)
      }

      // Recurse in subclasses
      for (cls <- subclasses)
        cls.walkForChanges(getClassInfo, getClassTreeIfChanged,
            methodAttributeChanges)
    }

    /** UPDATE PASS ONLY. */
    def walkForAdditions(
        getNewChildren: String => GenIterable[Analysis.ClassInfo],
        getClassTreeIfChanged: GetClassTreeIfChanged): Unit = {

      val subclassAcc = CollOps.prepAdd(subclasses)

      for (classInfo <- getNewChildren(encodedName)) {
        val cls = new Class(Some(this), classInfo.encodedName)
        CollOps.add(subclassAcc, cls)
        classes += classInfo.encodedName -> cls
        cls.setupAfterCreation(classInfo, getClassTreeIfChanged)
        cls.walkForAdditions(getNewChildren, getClassTreeIfChanged)
      }

      subclasses = CollOps.finishAdd(subclassAcc)
    }

    /** UPDATE PASS ONLY. */
    def updateHasElidableModuleAccessor(): Unit = {
      hasElidableModuleAccessor =
        isAdHocElidableModuleAccessor(encodedName) ||
        (isModuleClass && lookupMethod("init___").exists(isElidableModuleConstructor))
    }

    /** UPDATE PASS ONLY. */
    def updateIsInlineable(classInfo: Analysis.ClassInfo): Boolean = {
      val oldTryNewInlineable = tryNewInlineable
      isInlineable = optimizerHints.inline
      if (!isInlineable) {
        tryNewInlineable = None
      } else {
        val allFields = reverseParentChain.flatMap(_.fields)
        val (fieldValues, fieldTypes) = (for {
          VarDef(Ident(name, originalName), tpe, mutable, rhs) <- allFields
        } yield {
          (rhs, RecordType.Field(name, originalName, tpe, mutable))
        }).unzip
        tryNewInlineable = Some(
            RecordValue(RecordType(fieldTypes), fieldValues)(Position.NoPosition))
      }
      tryNewInlineable != oldTryNewInlineable
    }

    /** UPDATE PASS ONLY. */
    def setupAfterCreation(classInfo: Analysis.ClassInfo,
        getClassTreeIfChanged: GetClassTreeIfChanged): Unit = {

      updateWith(classInfo, getClassTreeIfChanged)
      interfaces =
        classInfo.ancestors.map(info => getInterface(info.encodedName)).toSet

      isInstantiated = classInfo.isInstantiated

      if (batchMode) {
        if (isInstantiated) {
          /* Only add the class to all its ancestor interfaces */
          for (intf <- interfaces)
            intf.addInstantiatedSubclass(this)
        }
      } else {
        val allMethodNames = allMethods().keys

        if (isInstantiated) {
          /* Add the class to all its ancestor interfaces + notify all callers
           * of any of the methods.
           * TODO: be more selective on methods that are notified: it is not
           * necessary to modify callers of methods defined in a parent class
           * that already existed in the previous run.
           */
          for (intf <- interfaces) {
            intf.addInstantiatedSubclass(this)
            for (methodName <- allMethodNames)
              intf.tagDynamicCallersOf(methodName)
          }
        }

        /* Tag static callers because the class could have been *moved*,
         * not just added.
         */
        for (methodName <- allMethodNames)
          myInterface.tagStaticCallersOf(methodName)
      }

      updateHasElidableModuleAccessor()
      updateIsInlineable(classInfo)
    }

    /** UPDATE PASS ONLY. */
    private def isElidableModuleConstructor(impl: MethodImpl): Boolean = {
      def isTriviallySideEffectFree(tree: Tree): Boolean = tree match {
        case _:VarRef | _:Literal | _:This => true
        case _                             => false
      }
      def isElidableStat(tree: Tree): Boolean = tree match {
        case Block(stats) =>
          stats.forall(isElidableStat)
        case Assign(Select(This(), _), rhs) =>
          isTriviallySideEffectFree(rhs)
        case ApplyStatic(ClassType(cls), methodName, List(This())) =>
          statics(cls).methods(methodName.name).originalDef.body match {
            case Skip() => true
            case _      => false
          }
        case ApplyStatically(This(), ClassType(cls), methodName, args) =>
          Definitions.isConstructorName(methodName.name) &&
          args.forall(isTriviallySideEffectFree) &&
          impl.owner.asInstanceOf[Class].superClass.exists { superCls =>
            superCls.encodedName == cls &&
            superCls.lookupMethod(methodName.name).exists(isElidableModuleConstructor)
          }
        case StoreModule(_, _) =>
          true
        case _ =>
          isTriviallySideEffectFree(tree)
      }
      isElidableStat(impl.originalDef.body)
    }

    /** All the methods of this class, including inherited ones.
     *  It has () so we remember this is an expensive operation.
     *  UPDATE PASS ONLY.
     */
    def allMethods(): scala.collection.Map[String, MethodImpl] = {
      val result = mutable.Map.empty[String, MethodImpl]
      for (parent <- reverseParentChain)
        result ++= parent.methods
      result
    }

    /** BOTH PASSES. */
    @tailrec
    final def lookupMethod(methodName: String): Option[MethodImpl] = {
      methods.get(methodName) match {
        case Some(impl) => Some(impl)
        case none =>
          superClass match {
            case Some(p) => p.lookupMethod(methodName)
            case none    => None
          }
      }
    }
  }

  /** Namespace for static members of a class. */
  class StaticsNamespace(_encodedName: String) extends MethodContainer(
      _encodedName, isStatic = true) {
    def thisType: Type = NoType
  }

  /** Thing from which a [[MethodImpl]] can unregister itself from. */
  trait Unregisterable {
    /** UPDATE PASS ONLY. */
    def unregisterDependee(dependee: MethodImpl): Unit
  }

  /** Type of a class or interface.
   *  Types are created on demand when a method is called on a given
   *  [[ClassType]].
   *
   *  Fully concurrency safe unless otherwise noted.
   */
  abstract class InterfaceType(val encodedName: String) extends Unregisterable {

    override def toString(): String =
      s"intf $encodedName"

    /** PROCESS PASS ONLY. Concurrency safe except with
     *  [[addInstantiatedSubclass]] and [[removeInstantiatedSubclass]]
     */
    def instantiatedSubclasses: Iterable[Class]

    /** UPDATE PASS ONLY. Concurrency safe except with
     *  [[instantiatedSubclasses]]
     */
    def addInstantiatedSubclass(x: Class): Unit

    /** UPDATE PASS ONLY. Concurrency safe except with
     *  [[instantiatedSubclasses]]
     */
    def removeInstantiatedSubclass(x: Class): Unit

    /** PROCESS PASS ONLY. Concurrency safe except with [[ancestors_=]] */
    def ancestors: List[String]

    /** UPDATE PASS ONLY. Not concurrency safe. */
    def ancestors_=(v: List[String]): Unit

    /** PROCESS PASS ONLY. Concurrency safe except with [[ancestors_=]]. */
    def registerAskAncestors(asker: MethodImpl): Unit

    /** PROCESS PASS ONLY. */
    def registerDynamicCaller(methodName: String, caller: MethodImpl): Unit

    /** PROCESS PASS ONLY. */
    def registerStaticCaller(methodName: String, caller: MethodImpl): Unit

    /** PROCESS PASS ONLY. */
    def registerCallerOfStatic(methodName: String, caller: MethodImpl): Unit

    /** UPDATE PASS ONLY. */
    def tagDynamicCallersOf(methodName: String): Unit

    /** UPDATE PASS ONLY. */
    def tagStaticCallersOf(methodName: String): Unit

    /** UPDATE PASS ONLY. */
    def tagCallersOfStatic(methodName: String): Unit
  }

  /** A method implementation.
   *  It must be concrete, and belong either to a [[Class]] or a [[TraitImpl]].
   *
   *  A single instance is **not** concurrency safe (unless otherwise noted in
   *  a method comment). However, the global state modifications are
   *  concurrency safe.
   */
  abstract class MethodImpl(val owner: MethodContainer,
      val encodedName: String) extends OptimizerCore.MethodImpl
                                  with OptimizerCore.AbstractMethodID
                                  with Unregisterable {
    private[this] var _deleted: Boolean = false

    var optimizerHints: OptimizerHints = OptimizerHints.empty
    var originalDef: MethodDef = _
    var desugaredDef: JSTree = _
    var preciseInfo: Infos.MethodInfo = _

    def thisType: Type = owner.thisType
    def deleted: Boolean = _deleted

    override def toString(): String =
      s"$owner.$encodedName"

    /** PROCESS PASS ONLY. */
    def registerBodyAsker(asker: MethodImpl): Unit

    /** UPDATE PASS ONLY. */
    def tagBodyAskers(): Unit

    /** PROCESS PASS ONLY. */
    private def registerAskAncestors(intf: InterfaceType): Unit = {
      intf.registerAskAncestors(this)
      registeredTo(intf)
    }

    /** PROCESS PASS ONLY. */
    private def registerDynamicCall(intf: InterfaceType,
        methodName: String): Unit = {
      intf.registerDynamicCaller(methodName, this)
      registeredTo(intf)
    }

    /** PROCESS PASS ONLY. */
    private def registerStaticCall(intf: InterfaceType,
        methodName: String): Unit = {
      intf.registerStaticCaller(methodName, this)
      registeredTo(intf)
    }

    /** PROCESS PASS ONLY. */
    private def registerCallStatic(intf: InterfaceType,
        methodName: String): Unit = {
      intf.registerCallerOfStatic(methodName, this)
      registeredTo(intf)
    }

    /** PROCESS PASS ONLY. */
    def registerAskBody(target: MethodImpl): Unit = {
      target.registerBodyAsker(this)
      registeredTo(target)
    }

    /** PROCESS PASS ONLY. */
    protected def registeredTo(intf: Unregisterable): Unit

    /** UPDATE PASS ONLY. */
    protected def unregisterFromEverywhere(): Unit

    /** Return true iff this is the first time this method is called since the
     *  last reset (via [[resetTag]]).
     *  UPDATE PASS ONLY.
     */
    protected def protectTag(): Boolean

    /** PROCESS PASS ONLY. */
    protected def resetTag(): Unit

    /** Returns true if the method's attributes changed.
     *  Attributes are whether it is inlineable, and whether it is a trait
     *  impl forwarder. Basically this is what is declared in
     *  [[OptimizerCore.AbstractMethodID]].
     *  In the process, tags all the body askers if the body changes.
     *  UPDATE PASS ONLY. Not concurrency safe on same instance.
     */
    def updateWith(methodInfo: Analysis.MethodInfo,
        methodDef: MethodDef): Boolean = {
      assert(!_deleted, "updateWith() called on a deleted method")

      val changed = {
        originalDef == null ||
        (methodDef.hash zip originalDef.hash).forall {
          case (h1, h2) => !Hashers.hashesEqual(h1, h2, considerPositions)
        }
      }

      if (changed) {
        tagBodyAskers()

        val oldAttributes = (inlineable, isTraitImplForwarder)

        optimizerHints = methodDef.optimizerHints
        originalDef = methodDef
        desugaredDef = null
        preciseInfo = null
        updateInlineable()
        tag()

        val newAttributes = (inlineable, isTraitImplForwarder)
        newAttributes != oldAttributes
      } else {
        false
      }
    }

    /** UPDATE PASS ONLY. Not concurrency safe on same instance. */
    def delete(): Unit = {
      assert(!_deleted, "delete() called twice")
      _deleted = true
      if (protectTag())
        unregisterFromEverywhere()
    }

    /** Concurrency safe with itself and [[delete]] on the same instance
     *
     *  [[tag]] can be called concurrently with [[delete]] when methods in
     *  traits/classes are updated.
     *
     *  UPDATE PASS ONLY.
     */
    def tag(): Unit = if (protectTag()) {
      scheduleMethod(this)
      unregisterFromEverywhere()
    }

    /** PROCESS PASS ONLY. */
    def process(): Unit = if (!_deleted) {
      val (optimizedDef, info) = new Optimizer().optimize(thisType, originalDef)
      desugaredDef = classEmitter.genMethod(owner.encodedName, optimizedDef)
      preciseInfo = info
      resetTag()
    }

    /** All methods are PROCESS PASS ONLY */
    private class Optimizer extends OptimizerCore(semantics) {
      type MethodID = MethodImpl

      val myself: MethodImpl.this.type = MethodImpl.this

      protected def getMethodBody(method: MethodID): MethodDef = {
        MethodImpl.this.registerAskBody(method)
        method.originalDef
      }

      protected def dynamicCall(intfName: String,
          methodName: String): List[MethodID] = {
        val intf = getInterface(intfName)
        MethodImpl.this.registerDynamicCall(intf, methodName)
        intf.instantiatedSubclasses.flatMap(_.lookupMethod(methodName)).toList
      }

      protected def staticCall(className: String,
          methodName: String): Option[MethodID] = {
        val clazz = classes(className)
        MethodImpl.this.registerStaticCall(clazz.myInterface, methodName)
        clazz.lookupMethod(methodName)
      }

      protected def callStatic(className: String,
          methodName: String): Option[MethodID] = {
        val staticsNS = statics(className)
        registerCallStatic(staticsNS.myInterface, methodName)
        staticsNS.methods.get(methodName)
      }

      protected def getAncestorsOf(intfName: String): List[String] = {
        val intf = getInterface(intfName)
        registerAskAncestors(intf)
        intf.ancestors
      }

      protected def hasElidableModuleAccessor(moduleClassName: String): Boolean =
        classes(moduleClassName).hasElidableModuleAccessor

      protected def tryNewInlineableClass(className: String): Option[RecordValue] =
        classes(className).tryNewInlineable
    }
  }

}

object GenIncOptimizer {

  private val isAdHocElidableModuleAccessor =
    Set("s_Predef$")

  private[optimizer] def logTime[A](logger: Logger,
      title: String)(body: => A): A = {
    val startTime = System.nanoTime()
    val result = body
    val endTime = System.nanoTime()
    val elapsedTime = endTime - startTime
    logger.time(title, elapsedTime)
    result
  }

  private[optimizer] trait AbsCollOps {
    type Map[K, V] <: mutable.Map[K, V]
    type ParMap[K, V] <: GenMap[K, V]
    type AccMap[K, V]
    type ParIterable[V] <: GenIterableLike[V, ParIterable[V]]
    type Addable[V]

    def emptyAccMap[K, V]: AccMap[K, V]
    def emptyMap[K, V]: Map[K, V]
    def emptyParMap[K, V]: ParMap[K, V]
    def emptyParIterable[V]: ParIterable[V]

    // Operations on ParMap
    def put[K, V](map: ParMap[K, V], k: K, v: V): Unit
    def remove[K, V](map: ParMap[K, V], k: K): Option[V]
    def retain[K, V](map: ParMap[K, V])(p: (K, V) => Boolean): Unit

    // Operations on AccMap
    def acc[K, V](map: AccMap[K, V], k: K, v: V): Unit
    def getAcc[K, V](map: AccMap[K, V], k: K): GenIterable[V]
    def parFlatMapKeys[A, B](map: AccMap[A, _])(
        f: A => GenTraversableOnce[B]): GenIterable[B]

    // Operations on ParIterable
    def prepAdd[V](it: ParIterable[V]): Addable[V]
    def add[V](addable: Addable[V], v: V): Unit
    def finishAdd[V](addable: Addable[V]): ParIterable[V]

  }

}
