/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js tools             **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2014, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package org.scalajs.core.tools.linker.analyzer

import scala.collection.mutable

import org.scalajs.core.ir.ClassKind
import org.scalajs.core.ir.Definitions._
import org.scalajs.core.ir.Traversers._
import org.scalajs.core.ir.Trees._
import org.scalajs.core.ir.Types._

import org.scalajs.core.tools.linker.LinkedClass
import org.scalajs.core.tools.linker.backend.emitter.Transients._

object Infos {

  /** Name used for infos of top-level exports. */
  private val TopLevelExportsName = "__topLevelExports"

  final class ClassInfo private (
      val encodedName: String,
      val isExported: Boolean,
      val kind: ClassKind,
      val superClass: Option[String], // always None for interfaces
      val interfaces: List[String], // direct parent interfaces only
      val methods: List[MethodInfo],
      val topLevelExportNames: List[String]
  )

  object ClassInfo {
    def apply(
        encodedName: String,
        isExported: Boolean = false,
        kind: ClassKind = ClassKind.Class,
        superClass: Option[String] = None,
        interfaces: List[String] = Nil,
        methods: List[MethodInfo] = Nil,
        topLevelExportNames: List[String] = Nil): ClassInfo = {
      new ClassInfo(encodedName, isExported, kind, superClass,
          interfaces, methods, topLevelExportNames)
    }
  }

  final class MethodInfo private (
      val encodedName: String,
      val isStatic: Boolean,
      val isAbstract: Boolean,
      val isExported: Boolean,
      val staticFieldsRead: Map[String, List[String]],
      val staticFieldsWritten: Map[String, List[String]],
      val methodsCalled: Map[String, List[String]],
      val methodsCalledStatically: Map[String, List[String]],
      val staticMethodsCalled: Map[String, List[String]],
      /** For a Scala class, it is instantiated with a `New`; for a JS class,
       *  its constructor is accessed with a `JSLoadConstructor`.
       */
      val instantiatedClasses: List[String],
      val accessedModules: List[String],
      val usedInstanceTests: List[String],
      val accessedClassData: List[String],
      val additionalMentionedClasses: List[String]
  )

  object MethodInfo {
    def apply(
        encodedName: String,
        isStatic: Boolean,
        isAbstract: Boolean,
        isExported: Boolean,
        staticFieldsRead: Map[String, List[String]],
        staticFieldsWritten: Map[String, List[String]],
        methodsCalled: Map[String, List[String]],
        methodsCalledStatically: Map[String, List[String]],
        staticMethodsCalled: Map[String, List[String]],
        instantiatedClasses: List[String],
        accessedModules: List[String],
        usedInstanceTests: List[String],
        accessedClassData: List[String],
        additionalMentionedClasses: List[String]): MethodInfo = {
      new MethodInfo(encodedName, isStatic, isAbstract, isExported,
          staticFieldsRead, staticFieldsWritten,
          methodsCalled, methodsCalledStatically, staticMethodsCalled,
          instantiatedClasses, accessedModules, usedInstanceTests,
          accessedClassData, additionalMentionedClasses)
    }
  }

  final class ClassInfoBuilder {
    private var encodedName: String = ""
    private var kind: ClassKind = ClassKind.Class
    private var isExported: Boolean = false
    private var superClass: Option[String] = None
    private val interfaces = mutable.ListBuffer.empty[String]
    private val methods = mutable.ListBuffer.empty[MethodInfo]
    private var topLevelExportNames: List[String] = Nil

    def setEncodedName(encodedName: String): this.type = {
      this.encodedName = encodedName
      this
    }

    def setKind(kind: ClassKind): this.type = {
      this.kind = kind
      this
    }

    def setIsExported(isExported: Boolean): this.type = {
      this.isExported = isExported
      this
    }

    def setSuperClass(superClass: Option[String]): this.type = {
      this.superClass = superClass
      this
    }

    def addInterface(interface: String): this.type = {
      interfaces += interface
      this
    }

    def addInterfaces(interfaces: TraversableOnce[String]): this.type = {
      this.interfaces ++= interfaces
      this
    }

    def addMethod(methodInfo: MethodInfo): this.type = {
      methods += methodInfo
      this
    }

    def setTopLevelExportNames(names: List[String]): this.type = {
      topLevelExportNames = names
      this
    }

    def result(): ClassInfo = {
      ClassInfo(encodedName, isExported, kind, superClass,
          interfaces.toList, methods.toList, topLevelExportNames)
    }
  }

  final class MethodInfoBuilder {
    private var encodedName: String = ""
    private var isStatic: Boolean = false
    private var isAbstract: Boolean = false
    private var isExported: Boolean = false

    private val staticFieldsRead = mutable.Map.empty[String, mutable.Set[String]]
    private val staticFieldsWritten = mutable.Map.empty[String, mutable.Set[String]]
    private val methodsCalled = mutable.Map.empty[String, mutable.Set[String]]
    private val methodsCalledStatically = mutable.Map.empty[String, mutable.Set[String]]
    private val staticMethodsCalled = mutable.Map.empty[String, mutable.Set[String]]
    private val instantiatedClasses = mutable.Set.empty[String]
    private val accessedModules = mutable.Set.empty[String]
    private val usedInstanceTests = mutable.Set.empty[String]
    private val accessedClassData = mutable.Set.empty[String]
    private val additionalMentionedClasses = mutable.Set.empty[String]

    def setEncodedName(encodedName: String): this.type = {
      this.encodedName = encodedName
      this
    }

    def setIsStatic(isStatic: Boolean): this.type = {
      this.isStatic = isStatic
      this
    }

    def setIsAbstract(isAbstract: Boolean): this.type = {
      this.isAbstract = isAbstract
      this
    }

    def setIsExported(isExported: Boolean): this.type = {
      this.isExported = isExported
      this
    }

    def addStaticFieldRead(cls: String, field: String): this.type = {
      staticFieldsRead.getOrElseUpdate(cls, mutable.Set.empty) += field
      this
    }

    def addStaticFieldWritten(cls: String, field: String): this.type = {
      staticFieldsWritten.getOrElseUpdate(cls, mutable.Set.empty) += field
      this
    }

    def addMethodCalled(receiverTpe: Type, method: String): this.type = {
      receiverTpe match {
        case ClassType(cls) => addMethodCalled(cls, method)
        case AnyType        => addMethodCalled(ObjectClass, method)
        case UndefType      => addMethodCalled(BoxedUnitClass, method)
        case BooleanType    => addMethodCalled(BoxedBooleanClass, method)
        case CharType       => addMethodCalled(BoxedCharacterClass, method)
        case ByteType       => addMethodCalled(BoxedByteClass, method)
        case ShortType      => addMethodCalled(BoxedShortClass, method)
        case IntType        => addMethodCalled(BoxedIntegerClass, method)
        case LongType       => addMethodCalled(BoxedLongClass, method)
        case FloatType      => addMethodCalled(BoxedFloatClass, method)
        case DoubleType     => addMethodCalled(BoxedDoubleClass, method)
        case StringType     => addMethodCalled(BoxedStringClass, method)

        case ArrayType(_) =>
          /* The pseudo Array class is not reified in our analyzer/analysis,
           * so we need to cheat here.
           * In the Array[T] class family, only clone__O is defined and
           * overrides j.l.Object.clone__O. Since this method is implemented
           * in scalajsenv.js and always kept, we can ignore it.
           * All other methods resolve to their definition in Object, so we
           * can model their reachability by calling them statically in the
           * Object class.
           */
          if (method != "clone__O")
            addMethodCalledStatically(ObjectClass, method)

        case NullType | NothingType =>
          // Nothing to do

        case NoType | RecordType(_) =>
          throw new IllegalArgumentException(
              s"Illegal receiver type: $receiverTpe")
      }

      this
    }

    def addMethodCalled(cls: String, method: String): this.type = {
      methodsCalled.getOrElseUpdate(cls, mutable.Set.empty) += method
      this
    }

    def addMethodCalledStatically(cls: String, method: String): this.type = {
      methodsCalledStatically.getOrElseUpdate(cls, mutable.Set.empty) += method
      this
    }

    def addStaticMethodCalled(cls: String, method: String): this.type = {
      staticMethodsCalled.getOrElseUpdate(cls, mutable.Set.empty) += method
      this
    }

    def addInstantiatedClass(cls: String): this.type = {
      instantiatedClasses += cls
      this
    }

    def addInstantiatedClass(cls: String, ctor: String): this.type =
      addInstantiatedClass(cls).addMethodCalledStatically(cls, ctor)

    def addAccessedModule(cls: String): this.type = {
      accessedModules += cls
      this
    }

    def addUsedInstanceTest(tpe: TypeRef): this.type =
      addUsedInstanceTest(baseNameOf(tpe))

    def addUsedInstanceTest(cls: String): this.type = {
      usedInstanceTests += cls
      this
    }

    def addAccessedClassData(tpe: TypeRef): this.type =
      addAccessedClassData(baseNameOf(tpe))

    def addAccessedClassData(cls: String): this.type = {
      accessedClassData += cls
      this
    }

    def addAdditionalMentionedClass(tpe: Type): this.type = {
      tpe match {
        case ClassType(cls)                  => addAdditionalMentionedClass(cls)
        case ArrayType(ArrayTypeRef(cls, _)) => addAdditionalMentionedClass(cls)
        case _                               => this
      }
    }

    def addAdditionalMentionedClass(tpe: TypeRef): this.type =
      addAdditionalMentionedClass(baseNameOf(tpe))

    def addAdditionalMentionedClass(cls: String): this.type = {
      additionalMentionedClasses += cls
      this
    }

    private def baseNameOf(tpe: TypeRef): String = tpe match {
      case ClassRef(name)        => name
      case ArrayTypeRef(base, _) => base
    }

    def result(): MethodInfo = {
      def toMapOfLists(
          m: mutable.Map[String, mutable.Set[String]]): Map[String, List[String]] = {
        m.mapValues(_.toList).toMap
      }

      additionalMentionedClasses --= staticFieldsRead.keys
      additionalMentionedClasses --= staticFieldsWritten.keys
      additionalMentionedClasses --= methodsCalled.keys
      additionalMentionedClasses --= methodsCalledStatically.keys
      additionalMentionedClasses --= staticMethodsCalled.keys
      additionalMentionedClasses --= instantiatedClasses
      additionalMentionedClasses --= accessedModules
      additionalMentionedClasses --= usedInstanceTests
      additionalMentionedClasses --= accessedClassData

      MethodInfo(
          encodedName = encodedName,
          isStatic = isStatic,
          isAbstract = isAbstract,
          isExported = isExported,
          staticFieldsRead = toMapOfLists(staticFieldsRead),
          staticFieldsWritten = toMapOfLists(staticFieldsWritten),
          methodsCalled = toMapOfLists(methodsCalled),
          methodsCalledStatically = toMapOfLists(methodsCalledStatically),
          staticMethodsCalled = toMapOfLists(staticMethodsCalled),
          instantiatedClasses = instantiatedClasses.toList,
          accessedModules = accessedModules.toList,
          usedInstanceTests = usedInstanceTests.toList,
          accessedClassData = accessedClassData.toList,
          additionalMentionedClasses = additionalMentionedClasses.toList
      )
    }
  }

  /** Generates the [[ClassInfo]] of a
   *  [[org.scalajs.core.ir.Trees.ClassDef Trees.ClassDef]].
   */
  def generateClassInfo(classDef: ClassDef): ClassInfo = {
    val builder = new ClassInfoBuilder()
      .setEncodedName(classDef.name.name)
      .setKind(classDef.kind)
      .setSuperClass(classDef.superClass.map(_.name))
      .addInterfaces(classDef.interfaces.map(_.name))

    classDef.memberDefs foreach {
      case fieldDef: FieldDef =>
      case methodDef: MethodDef =>
        builder.addMethod(generateMethodInfo(methodDef))
      case propertyDef: PropertyDef =>
        builder.addMethod(generatePropertyInfo(propertyDef))
    }

    if (classDef.topLevelExportDefs.nonEmpty) {
      builder.setIsExported(true)

      val optInfo = generateTopLevelExportsInfo(classDef.name.name,
          classDef.topLevelExportDefs)
      optInfo.foreach(builder.addMethod(_))

      val names = classDef.topLevelExportDefs.map(_.topLevelExportName)
      builder.setTopLevelExportNames(names)
    }

    builder.result()
  }

  /** Generates the [[MethodInfo]] of a
   *  [[org.scalajs.core.ir.Trees.MethodDef Trees.MethodDef]].
   */
  def generateMethodInfo(methodDef: MethodDef): MethodInfo =
    new GenInfoTraverser().generateMethodInfo(methodDef)

  /** Generates the [[MethodInfo]] of a
   *  [[org.scalajs.core.ir.Trees.PropertyDef Trees.PropertyDef]].
   */
  def generatePropertyInfo(propertyDef: PropertyDef): MethodInfo =
    new GenInfoTraverser().generatePropertyInfo(propertyDef)

  /** Generates the [[MethodInfo]] for the top-level exports. */
  def generateTopLevelExportsInfo(enclosingClass: String,
      topLevelExportDefs: List[TopLevelExportDef]): Option[MethodInfo] = {

    var exportedConstructors: List[TopLevelConstructorExportDef] = Nil
    var topLevelMethodExports: List[TopLevelMethodExportDef] = Nil
    var topLevelFieldExports: List[TopLevelFieldExportDef] = Nil

    topLevelExportDefs.foreach {
      case constructorDef: TopLevelConstructorExportDef =>
        exportedConstructors ::= constructorDef
      case _:TopLevelJSClassExportDef | _:TopLevelModuleExportDef =>
      case topLevelMethodExport: TopLevelMethodExportDef =>
        topLevelMethodExports ::= topLevelMethodExport
      case topLevelFieldExport: TopLevelFieldExportDef =>
        topLevelFieldExports ::= topLevelFieldExport
    }

    if (exportedConstructors.nonEmpty || topLevelMethodExports.nonEmpty ||
        topLevelFieldExports.nonEmpty) {
      Some(new GenInfoTraverser().generateTopLevelExportsInfo(enclosingClass,
          exportedConstructors, topLevelMethodExports, topLevelFieldExports))
    } else {
      None
    }
  }

  private final class GenInfoTraverser extends Traverser {
    private val builder = new MethodInfoBuilder

    def generateMethodInfo(methodDef: MethodDef): MethodInfo = {
      builder
        .setEncodedName(methodDef.name.encodedName)
        .setIsStatic(methodDef.static)
        .setIsAbstract(methodDef.body.isEmpty)
        .setIsExported(!methodDef.name.isInstanceOf[Ident])

      methodDef.name match {
        case Ident(encodedName, _) =>
          val sig = decodeMethodName(encodedName)
          for (paramTypeRef <- sig._2)
            builder.addAdditionalMentionedClass(paramTypeRef)
          for (resultTypeRef <- sig._3)
            builder.addAdditionalMentionedClass(resultTypeRef)
        case ComputedName(tree, _) =>
          traverse(tree)
        case StringLiteral(_) =>
      }

      for (paramDef <- methodDef.args)
        builder.addAdditionalMentionedClass(paramDef.ptpe)

      methodDef.body.foreach(traverse)

      builder.result()
    }

    def generatePropertyInfo(propertyDef: PropertyDef): MethodInfo = {
      builder
        .setEncodedName(propertyDef.name.encodedName)
        .setIsStatic(propertyDef.static)
        .setIsExported(true)

      propertyDef.name match {
        case ComputedName(tree, _) =>
          traverse(tree)
        case _ =>
      }

      propertyDef.getterBody.foreach(traverse)
      propertyDef.setterArgAndBody.foreach { case (arg, body) =>
        builder.addAdditionalMentionedClass(arg.ptpe)
        traverse(body)
      }

      builder.result()
    }

    def generateTopLevelExportsInfo(enclosingClass: String,
        topLevelConstructorDefs: List[TopLevelConstructorExportDef],
        topLevelMethodExports: List[TopLevelMethodExportDef],
        topLevelFieldExports: List[TopLevelFieldExportDef]): MethodInfo = {
      builder
        .setEncodedName(TopLevelExportsName)
        .setIsExported(true)

      for (topLevelConstructorDef <- topLevelConstructorDefs)
        traverse(topLevelConstructorDef.body)

      for (topLevelMethodExport <- topLevelMethodExports)
        topLevelMethodExport.methodDef.body.foreach(traverse(_))

      for (topLevelFieldExport <- topLevelFieldExports) {
        val field = topLevelFieldExport.field.name
        builder.addStaticFieldRead(enclosingClass, field)
        builder.addStaticFieldWritten(enclosingClass, field)
      }

      builder.result()
    }

    override def traverse(tree: Tree): Unit = {
      tree match {
        /* Do not call super.traverse() so that the field is not also marked as
         * read.
         */
        case Assign(SelectStatic(ClassType(cls), Ident(field, _)), rhs) =>
          builder.addStaticFieldWritten(cls, field)
          traverse(rhs)

        // In all other cases, we'll have to call super.traverse()
        case _ =>
          tree match {
            case VarDef(_, vtpe, _, _) =>
              builder.addAdditionalMentionedClass(vtpe)
            case Closure(_, captureParams, _, _, _) =>
              for (paramDef <- captureParams)
                builder.addAdditionalMentionedClass(paramDef.ptpe)
            case _:Labeled | _:If | _:Match | _:TryCatch | _:TryFinally |
                _:Select | _:ArraySelect | _:RecordValue =>
              builder.addAdditionalMentionedClass(tree.tpe)

            case New(ClassType(cls), ctor, _) =>
              builder.addInstantiatedClass(cls, ctor.name)

            case SelectStatic(ClassType(cls), Ident(field, _)) =>
              builder.addStaticFieldRead(cls, field)

            case Apply(receiver, Ident(method, _), _) =>
              builder.addMethodCalled(receiver.tpe, method)
            case ApplyStatically(_, ClassType(cls), method, _) =>
              builder.addMethodCalledStatically(cls, method.name)
            case ApplyStatic(ClassType(cls), method, _) =>
              builder.addStaticMethodCalled(cls, method.name)

            case LoadModule(ClassType(cls)) =>
              builder.addAccessedModule(cls)

            case IsInstanceOf(_, tpe) =>
              builder.addUsedInstanceTest(tpe)
            case AsInstanceOf(_, tpe) =>
              builder.addUsedInstanceTest(tpe)

            case NewArray(tpe, _) =>
              builder.addAccessedClassData(tpe.arrayTypeRef)
            case ArrayValue(tpe, _) =>
              builder.addAccessedClassData(tpe.arrayTypeRef)
            case ClassOf(cls) =>
              builder.addAccessedClassData(cls)

            case LoadJSConstructor(cls) =>
              builder.addInstantiatedClass(cls.className)

            case LoadJSModule(ClassType(cls)) =>
              builder.addAccessedModule(cls)

            case CreateJSClass(cls, _) =>
              builder.addInstantiatedClass(cls.className)

            case Transient(CallHelper(_, args)) =>
              // This should only happen when called from the Refiner
              builder.addAdditionalMentionedClass(tree.tpe)
              args.foreach(traverse)

            case _ =>
          }

          super.traverse(tree)
      }
    }
  }

}
