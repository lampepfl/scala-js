/*
 * Scala.js (https://www.scala-js.org/)
 *
 * Copyright EPFL.
 *
 * Licensed under Apache License 2.0
 * (https://www.apache.org/licenses/LICENSE-2.0).
 *
 * See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.
 */

package org.scalajs.linker.backend.emitter

import scala.annotation.tailrec

import scala.collection.mutable

import org.scalajs.ir.{ClassKind, Position}
import org.scalajs.ir.Names._
import org.scalajs.ir.OriginalName.NoOriginalName
import org.scalajs.ir.Trees.{JSNativeLoadSpec, MemberNamespace}

import org.scalajs.logging._

import org.scalajs.linker.analyzer.ModuleAnalyzer
import org.scalajs.linker.interface._
import org.scalajs.linker.standard._
import org.scalajs.linker.backend.javascript.{Trees => js, _}
import org.scalajs.linker.CollectionsCompat.MutableMapCompatOps

import EmitterNames._
import GlobalRefUtils._

/** Emits a desugared JS tree to a builder */
final class Emitter private (config: CommonPhaseConfig,
    internalOptions: InternalOptions) {

  import Emitter._
  import config.coreSpec._

  def this(config: CommonPhaseConfig) = {
    this(config, InternalOptions())
  }

  private val knowledgeGuardian = new KnowledgeGuardian(config)

  private val nameGen: NameGen = new NameGen

  /** Dummy KnowledgeAccessor to generate uncached trees. */
  private val uncachedKnowledgeAccessor =
    new knowledgeGuardian.KnowledgeAccessor {}

  private class State(val lastMentionedDangerousGlobalRefs: Set[String]) {
    val jsGen: JSGen = {
      new JSGen(semantics, esFeatures, moduleKind, nameGen, internalOptions,
          lastMentionedDangerousGlobalRefs)
    }

    val classEmitter: ClassEmitter = new ClassEmitter(jsGen)

    val coreJSLibCache: CoreJSLibCache = new CoreJSLibCache

    val classCaches: mutable.Map[List[ClassName], ClassCache] = mutable.Map.empty
  }

  private var state: State = new State(Set.empty)

  private def jsGen: JSGen = state.jsGen
  private def classEmitter: ClassEmitter = state.classEmitter
  private def classCaches: mutable.Map[List[ClassName], ClassCache] = state.classCaches

  private[this] var statsClassesReused: Int = 0
  private[this] var statsClassesInvalidated: Int = 0
  private[this] var statsMethodsReused: Int = 0
  private[this] var statsMethodsInvalidated: Int = 0

  val symbolRequirements: SymbolRequirement =
    Emitter.symbolRequirements(config.coreSpec)

  val injectedIRFiles: Seq[IRFile] = PrivateLibHolder.files

  private val needsIIFEWrapper = {
    moduleKind match {
      case ModuleKind.NoModule                             => true
      case ModuleKind.ESModule | ModuleKind.CommonJSModule => false
    }
  }

  private def ifIIFE(str: String): String = if (needsIIFEWrapper) str else ""

  // Private API for the Closure backend (could be opened if necessary)
  private[backend] def withOptimizeBracketSelects(
      optimizeBracketSelects: Boolean): Emitter = {
    new Emitter(config,
        internalOptions.withOptimizeBracketSelects(optimizeBracketSelects))
  }

  // Private API for the Closure backend (could be opened if necessary)
  private[backend] def withTrackAllGlobalRefs(
      trackAllGlobalRefs: Boolean): Emitter = {
    new Emitter(config,
        internalOptions.withTrackAllGlobalRefs(trackAllGlobalRefs))
  }

  def emit(unit: LinkingUnit, logger: Logger): Map[Int, Result] = {
    emitInternal(unit, logger)
  }

  private def topLevelVarDeclarations(unit: LinkingUnit): List[String] = {
    moduleKind match {
      case ModuleKind.NoModule =>
        val topLevelExportNames = mutable.Set.empty[String]
        for {
          classDef <- unit.classDefs
          export <- classDef.topLevelExports
        } {
          topLevelExportNames += export.value.topLevelExportName
        }
        topLevelExportNames.toList

      case ModuleKind.ESModule | ModuleKind.CommonJSModule =>
        Nil
    }
  }

  private def emitInternal(unit: LinkingUnit, logger: Logger): Map[Int, Result] = {
    startRun(unit)
    try {
      val generatedClasses = {
        logger.time("Emitter: Generate classes") {
          genAllClasses(unit.classDefs, logger, secondAttempt = false)
            .filterNot(_.isEmpty)
            .map(x => x.name -> x)
            .toMap
        }
      }

      val moduleAnalysis = {
        logger.time("Emitter: Analyze Modules") {
          ModuleAnalyzer.analyze(generatedClasses.mapValues(_.classDeps))
        }
      }

      logger.time("Emitter: Write trees") {
        val WithInfo(coreJSLibTree, coreJSLibTrackedGlobalRefs, _) =
          state.coreJSLibCache.tree

        for (module <- moduleAnalysis.modules) yield {
          val trees = mutable.ListBuffer.empty[js.Tree]
          var globalRefs = Set.empty[String]
  
          if (module.deps.isEmpty) {
            // This is the root module.
            trees += coreJSLibTree
            //globalRefs = unionPreserveEmpty(globalRefs, coreJSLibTrackedGlobalRefs)
          }

          // TODO merge globalRefs

          implicit val pos = Position.NoPosition

          for ((mod, elems) <- module.deps) {
            val from = js.StringLiteral("%s.js".format(mod.toString))
            val bindings = elems.toList.sorted.map(x => (js.ExportName(x), js.Ident(x)))
            trees += js.Import(bindings, from)
          }

          // For now, we just emit all module imports everywhere.
          // TODO fix.
          emitModuleImports(unit.classDefs.iterator, trees, logger)

          val classes = module.classes
            .map(generatedClasses(_))
            .sorted

          emitGeneratedClasses(trees, classes)
          //classes.foreach(refs += _)
  
          // TODO fix
          //for (moduleInitializer <- unit.moduleInitializers)
          //  trees += classEmitter.genModuleInitializer(moduleInitializer)
  
          module.id -> new Result("", trees.result(), "", Nil, globalRefs)
        }
      }.toMap
    } finally {
      endRun(logger)
    }
  }

  private def emitGeneratedClasses(builder: mutable.ListBuffer[js.Tree],
      generatedClasses: Seq[GeneratedClass]): Unit = {
    /* Emit all the classes, in the appropriate order:
     *
     * 1. All class definitions, which depend on nothing but their
     *    superclasses.
     * 2. The initialization of $L0, the Long zero, which depends on the
     *    definition of the RuntimeLong class.
     * 3. All static field definitions, which depend on nothing, except those
     *    of type Long which need $L0.
     * 4. All static initializers, which in the worst case can observe some
     *    "zero" state of other static field definitions, but must not
     *    observe a *non-initialized* (undefined) state.
     * 5. All the exports, during which some JS class creation can happen,
     *    causing JS static initializers to run. Those also must not observe
     *    a non-initialized state of other static fields.
     */
    for (generatedClass <- generatedClasses)
      builder ++= generatedClass.main

    //if (!jsGen.useBigIntForLongs)
    //  builder += emitInitializeL0()(uncachedKnowledgeAccessor)

    for (generatedClass <- generatedClasses)
      builder ++= generatedClass.staticFields

    for (generatedClass <- generatedClasses)
      builder ++= generatedClass.staticInitialization

    for (generatedClass <- generatedClasses)
      builder ++= generatedClass.topLevelExports
  }

  private def emitModuleImports(orderedClasses: Iterator[LinkedClass],
      builder: mutable.ListBuffer[js.Tree], logger: Logger): Unit = {

    def foreachImportedModule(f: (String, Position) => Unit): Unit = {
      val encounteredModuleNames = mutable.Set.empty[String]
      for (classDef <- orderedClasses) {
        def addModuleRef(module: String): Unit = {
          if (encounteredModuleNames.add(module))
            f(module, classDef.pos)
        }
        classDef.jsNativeLoadSpec match {
          case None =>
          case Some(JSNativeLoadSpec.Global(_, _)) =>
          case Some(JSNativeLoadSpec.Import(module, _)) =>
            addModuleRef(module)
          case Some(JSNativeLoadSpec.ImportWithGlobalFallback(
              JSNativeLoadSpec.Import(module, _), _)) =>
            addModuleRef(module)
        }
      }
    }

    moduleKind match {
      case ModuleKind.NoModule =>
        var importsFound: Boolean = false

        for (classDef <- orderedClasses) {
          classDef.jsNativeLoadSpec match {
            case Some(JSNativeLoadSpec.Import(module, _)) =>
              val displayName = classDef.className.nameString
              logger.error(s"$displayName needs to be imported from module " +
                  s"'$module' but module support is disabled.")
              importsFound = true

            case _ =>
              // ok
          }
        }

        if (importsFound) {
          throw new LinkingException(
              "There were module imports without fallback to global " +
              "variables, but module support is disabled.\n" +
              "To enable module support, set `scalaJSLinkerConfig ~= " +
              "(_.withModuleKind(ModuleKind.CommonJSModule))`.")
        }

      case ModuleKind.ESModule =>
        foreachImportedModule { (module, pos0) =>
          implicit val pos = pos0
          val from = js.StringLiteral(module)
          val moduleBinding = jsGen.fileLevelModuleField(module).ident
          val importStat = js.ImportNamespace(moduleBinding, from)
          builder += importStat
        }

      case ModuleKind.CommonJSModule =>
        foreachImportedModule { (module, pos0) =>
          implicit val pos = pos0
          val rhs = js.Apply(js.VarRef(js.Ident("require")),
              List(js.StringLiteral(module)))
          val lhs = jsGen.fileLevelModuleField(module)
          val decl = jsGen.genLet(lhs.ident, mutable = false, rhs)
          builder += decl
        }
    }
  }

  /** Emits the initialization of the global variable `$L0`, which holds the
   *  zero of type `Long`.
   */
  private def emitInitializeL0(): WithInfo[js.Tree] = {
    implicit val pos = Position.NoPosition
    implicit val globalKnowledge = uncachedKnowledgeAccessor

    // $L0 = new RuntimeLong(0, 0)
    for {
      rhs <- jsGen.genScalaClassNew(
          LongImpl.RuntimeLongClass, LongImpl.initFromParts,
          js.IntLiteral(0), js.IntLiteral(0))
    } yield {
      js.Assign(jsGen.coreJSLibVar("L0"), rhs)
    }
  }

  private def startRun(unit: LinkingUnit): Unit = {
    statsClassesReused = 0
    statsClassesInvalidated = 0
    statsMethodsReused = 0
    statsMethodsInvalidated = 0

    val invalidateAll = knowledgeGuardian.update(unit)
    if (invalidateAll) {
      state.coreJSLibCache.invalidate()
      classCaches.clear()
    }

    classCaches.valuesIterator.foreach(_.startRun())
  }

  private def endRun(logger: Logger): Unit = {
    logger.debug(
        s"Emitter: Class tree cache stats: reused: $statsClassesReused -- "+
        s"invalidated: $statsClassesInvalidated")
    logger.debug(
        s"Emitter: Method tree cache stats: reused: $statsMethodsReused -- "+
        s"invalidated: $statsMethodsInvalidated")
    classCaches.filterInPlace((_, c) => c.cleanAfterRun())
  }

  /** Generates all the desugared classes.
   *
   *  If, at the end of the process, the set of accessed dangerous globals has
   *  changed, invalidate *everything* and start over. If at first you don't
   *  succeed, ...
   */
  @tailrec
  private def genAllClasses(classes: List[LinkedClass], logger: Logger,
      secondAttempt: Boolean): List[GeneratedClass] = {

    val objectClass = classes.find(_.name.name == ObjectClass).get
    val generatedClasses = classes.map(genClass(_, objectClass))

    val trackedGlobalRefs = generatedClasses.foldLeft(Set.empty[String]) {
      (prev, generatedClass) =>
        unionPreserveEmpty(prev, generatedClass.trackedGlobalRefs)
    }

    val mentionedDangerousGlobalRefs =
      if (!internalOptions.trackAllGlobalRefs) trackedGlobalRefs
      else GlobalRefUtils.keepOnlyDangerousGlobalRefs(trackedGlobalRefs)

    if (mentionedDangerousGlobalRefs == state.lastMentionedDangerousGlobalRefs) {
      generatedClasses
    } else {
      assert(!secondAttempt,
          "Uh oh! The second attempt gave a different set of dangerous " +
          "global refs than the first one.")

      logger.debug(
          "Emitter: The set of dangerous global refs has changed. " +
          "Going to re-generate the world.")

      state = new State(mentionedDangerousGlobalRefs)
      genAllClasses(classes, logger, secondAttempt = true)
    }
  }

  private def genClass(linkedClass: LinkedClass,
      objectClass: LinkedClass): GeneratedClass = {
    val className = linkedClass.className
    val classCache = getClassCache(linkedClass.ancestors)
    val classTreeCache = classCache.getCache(linkedClass.version)
    val kind = linkedClass.kind

    // Global ref management

    var trackedGlobalRefs: Set[String] = Set.empty
    var trackedClassDeps: Map[ClassName, Set[String]] = Map.empty

    def extractWithInfo[A](withInfo: WithInfo[A]): A = {
      trackedGlobalRefs = unionPreserveEmpty(withInfo.globalVarNames, trackedGlobalRefs)

      for ((clazz, field) <- withInfo.classDeps) {
        val newFields = trackedClassDeps.getOrElse(clazz, Set.empty) + field
        trackedClassDeps = trackedClassDeps.updated(clazz, newFields)
      }

      withInfo.value
    }

    // Main part

    var main: List[js.Tree] = Nil

    def addToMainBase(tree: js.Tree): Unit = main ::= tree

    def addToMain(treeWithInfo: WithInfo[js.Tree]): Unit =
      addToMainBase(extractWithInfo(treeWithInfo))

    val (linkedInlineableInit, linkedMethods) =
      classEmitter.extractInlineableInit(linkedClass)(classCache)

    // Symbols for private JS fields
    if (kind.isJSClass) {
      val fieldDefs = classTreeCache.privateJSFields.getOrElseUpdate {
        classEmitter.genCreatePrivateJSFieldDefsOfJSClass(linkedClass)
      }
      fieldDefs.foreach(addToMainBase(_))
    }

    // Static-like methods
    for (m <- linkedMethods) {
      val methodDef = m.value
      val namespace = methodDef.flags.namespace

      if (namespace != MemberNamespace.Public) {
        val methodCache =
          classCache.getMethodCache(namespace, methodDef.methodName)

        addToMain(methodCache.getOrElseUpdate(m.version,
            classEmitter.genMethod(className, m.value)(methodCache)))
      }
    }

    // Class definition
    if (linkedClass.hasInstances && kind.isAnyNonNativeClass) {
      // JS constructor
      val ctor = {
        /* The constructor depends both on the class version, and the version
         * of the inlineable init, if there is one.
         */
        val ctorCache = classCache.getConstructorCache()
        val ctorVersion = linkedInlineableInit.fold[Option[String]] {
          linkedClass.version.map("1-" + _)
        } { linkedInit =>
          mergeVersions(linkedClass.version, linkedInit.version).map("2-" + _)
        }
        val initToInline = linkedInlineableInit.map(_.value)
        ctorCache.getOrElseUpdate(ctorVersion,
            classEmitter.genConstructor(linkedClass, initToInline)(ctorCache))
      }

      /* Bridges from Throwable to methods of Object, which are necessary
       * because Throwable is rewired to extend JavaScript's Error instead of
       * j.l.Object.
       */
      val linkedMethodsAndBridges = if (ClassEmitter.shouldExtendJSError(linkedClass)) {
        val existingMethods = linkedMethods
          .withFilter(_.value.flags.namespace == MemberNamespace.Public)
          .map(_.value.methodName)
          .toSet

        val bridges = for {
          m <- objectClass.methods
          if m.value.flags.namespace == MemberNamespace.Public
          methodName = m.value.methodName
          if !existingMethods.contains(methodName)
        } yield {
          import org.scalajs.ir.Trees._
          import org.scalajs.ir.Types._

          val methodDef = m.value
          implicit val pos = methodDef.pos

          val methodName = methodDef.name
          val newBody = ApplyStatically(ApplyFlags.empty,
              This()(ClassType(className)), ObjectClass, methodName,
              methodDef.args.map(_.ref))(
              methodDef.resultType)
          val newMethodDef = MethodDef(MemberFlags.empty, methodName,
              methodDef.originalName, methodDef.args, methodDef.resultType,
              Some(newBody))(
              OptimizerHints.empty, None)
          new Versioned(newMethodDef, m.version)
        }

        linkedMethods ++ bridges
      } else {
        linkedMethods
      }

      // Normal methods
      val memberMethods = for {
        m <- linkedMethodsAndBridges
        if m.value.flags.namespace == MemberNamespace.Public
      } yield {
        val methodCache =
          classCache.getMethodCache(MemberNamespace.Public, m.value.methodName)

        methodCache.getOrElseUpdate(m.version,
            classEmitter.genMethod(className, m.value)(methodCache))
      }

      // Exported Members
      val exportedMembers = classTreeCache.exportedMembers.getOrElseUpdate(
          classEmitter.genExportedMembers(linkedClass)(classCache))

      addToMain(classEmitter.buildClass(linkedClass, ctor, memberMethods,
          exportedMembers)(classCache))
    } else if (kind == ClassKind.Interface) {
      // Default methods
      for {
        m <- linkedMethods
        if m.value.flags.namespace == MemberNamespace.Public
      } yield {
        val methodCache =
          classCache.getMethodCache(MemberNamespace.Public, m.value.methodName)
        addToMain(methodCache.getOrElseUpdate(m.version,
            classEmitter.genDefaultMethod(className, m.value)(methodCache)))
      }
    } else if (kind == ClassKind.HijackedClass) {
      // Hijacked methods
      for {
        m <- linkedMethods
        if m.value.flags.namespace == MemberNamespace.Public
      } yield {
        val methodCache =
          classCache.getMethodCache(MemberNamespace.Public, m.value.methodName)
        addToMain(methodCache.getOrElseUpdate(m.version,
            classEmitter.genHijackedMethod(className, m.value)(methodCache)))
      }
    }

    if (classEmitter.needInstanceTests(linkedClass)) {
      if (!linkedClass.hasInstances && kind.isClass) {
        /* The isInstanceOf implementation will generate
         * `x instanceof $c_TheClass`, but `$c_TheClass` won't be declared at
         * all. Define it as a fake class to avoid `ReferenceError`s.
         */
        addToMainBase(classEmitter.genFakeClass(linkedClass))
      }

      addToMainBase(classTreeCache.instanceTests.getOrElseUpdate(js.Block(
          classEmitter.genInstanceTests(linkedClass),
          classEmitter.genArrayInstanceTests(linkedClass)
      )(linkedClass.pos)))
    }

    if (linkedClass.hasRuntimeTypeInfo) {
      addToMain(classTreeCache.typeData.getOrElseUpdate(
          classEmitter.genTypeData(linkedClass)(classCache)))
    }

    if (linkedClass.hasInstances && kind.isClass && linkedClass.hasRuntimeTypeInfo)
      addToMainBase(classTreeCache.setTypeData.getOrElseUpdate(
          classEmitter.genSetTypeData(linkedClass)))

    if (linkedClass.kind.hasModuleAccessor)
      addToMainBase(classTreeCache.moduleAccessor.getOrElseUpdate(
          classEmitter.genModuleAccessor(linkedClass)))

    // Static fields

    val staticFields = if (linkedClass.kind.isJSType) {
      Nil
    } else {
      val classCache = getClassCache(linkedClass.ancestors)
      val classTreeCache = classCache.getCache(linkedClass.version)

      classTreeCache.staticFields.getOrElseUpdate(
          classEmitter.genCreateStaticFieldsOfScalaClass(linkedClass)(classCache))
    }

    // Static initialization

    val staticInitialization = if (linkedClass.kind.isJSType) {
      Nil
    } else {
      classEmitter.genStaticInitialization(linkedClass)
    }

    // Top-level exports

    val topLevelExports = if (linkedClass.topLevelExports.isEmpty) {
      Nil
    } else {
      val treeWithInfo = classTreeCache.topLevelExports.getOrElseUpdate(
          classEmitter.genTopLevelExports(linkedClass)(classCache))
      extractWithInfo(treeWithInfo)
    }

    // Build the result

    new GeneratedClass(
        linkedClass.className,
        linkedClass.ancestors.size,
        main.reverse,
        staticFields,
        staticInitialization,
        topLevelExports,
        trackedGlobalRefs,
        trackedClassDeps
    )
  }

  // Helpers

  private def mergeVersions(v1: Option[String],
      v2: Option[String]): Option[String] = {
    v1.flatMap(s1 => v2.map(s2 => "" + s1.length + "-" + s1 + s2))
  }

  private def getClassCache(ancestors: List[ClassName]) =
    classCaches.getOrElseUpdate(ancestors, new ClassCache)

  // Caching

  private final class ClassCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _cache: DesugaredClassCache = null
    private[this] var _lastVersion: Option[String] = None
    private[this] var _cacheUsed = false

    private[this] val _methodCaches =
      Array.fill(MemberNamespace.Count)(mutable.Map.empty[MethodName, MethodCache])

    private[this] var _constructorCache: Option[MethodCache] = None

    override def invalidate(): Unit = {
      /* Do not invalidate contained methods, as they have their own
       * invalidation logic.
       */
      super.invalidate()
      _cache = null
      _lastVersion = None
    }

    def startRun(): Unit = {
      _cacheUsed = false
      _methodCaches.foreach(_.valuesIterator.foreach(_.startRun()))
      _constructorCache.foreach(_.startRun())
    }

    def getCache(version: Option[String]): DesugaredClassCache = {
      if (_cache == null || _lastVersion.isEmpty || _lastVersion != version) {
        invalidate()
        statsClassesInvalidated += 1
        _lastVersion = version
        _cache = new DesugaredClassCache
      } else {
        statsClassesReused += 1
      }
      _cacheUsed = true
      _cache
    }

    def getMethodCache(namespace: MemberNamespace,
        methodName: MethodName): MethodCache = {
      _methodCaches(namespace.ordinal)
        .getOrElseUpdate(methodName, new MethodCache)
    }

    def getConstructorCache(): MethodCache = {
      _constructorCache.getOrElse {
        val cache = new MethodCache
        _constructorCache = Some(cache)
        cache
      }
    }

    def cleanAfterRun(): Boolean = {
      _methodCaches.foreach(_.filterInPlace((_, c) => c.cleanAfterRun()))

      if (_constructorCache.exists(!_.cleanAfterRun()))
        _constructorCache = None

      if (!_cacheUsed)
        invalidate()

      _methodCaches.exists(_.nonEmpty) || _cacheUsed
    }
  }

  private final class MethodCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _tree: WithInfo[js.Tree] = null
    private[this] var _lastVersion: Option[String] = None
    private[this] var _cacheUsed = false

    override def invalidate(): Unit = {
      super.invalidate()
      _tree = null
      _lastVersion = None
    }

    def startRun(): Unit = _cacheUsed = false

    def getOrElseUpdate(version: Option[String],
        v: => WithInfo[js.Tree]): WithInfo[js.Tree] = {
      if (_tree == null || _lastVersion.isEmpty || _lastVersion != version) {
        invalidate()
        statsMethodsInvalidated += 1
        _tree = v
        _lastVersion = version
      } else {
        statsMethodsReused += 1
      }
      _cacheUsed = true
      _tree
    }

    def cleanAfterRun(): Boolean = {
      if (!_cacheUsed)
        invalidate()

      _cacheUsed
    }
  }

  private class CoreJSLibCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _tree: WithInfo[js.Tree] = _

    def tree: WithInfo[js.Tree] = {
      if (_tree == null)
        _tree = CoreJSLib.build(jsGen, this)
      _tree
    }

    override def invalidate(): Unit = {
      super.invalidate()
      _tree = null
    }
  }
}

object Emitter {
  /** Result of an emitter run. */
  final class Result private[Emitter](
      val header: String,
      val body: List[js.Tree],
      val footer: String,
      val topLevelVarDecls: List[String],
      val globalRefs: Set[String]
  )

  private final class DesugaredClassCache {
    val privateJSFields = new OneTimeCache[List[js.Tree]]
    val exportedMembers = new OneTimeCache[WithInfo[js.Tree]]
    val instanceTests = new OneTimeCache[js.Tree]
    val typeData = new OneTimeCache[WithInfo[js.Tree]]
    val setTypeData = new OneTimeCache[js.Tree]
    val moduleAccessor = new OneTimeCache[js.Tree]
    val staticFields = new OneTimeCache[List[js.Tree]]
    val topLevelExports = new OneTimeCache[WithInfo[List[js.Tree]]]
  }

  private final class GeneratedClass(
      val name: ClassName,
      private val ancestorCount: Int,
      val main: List[js.Tree],
      val staticFields: List[js.Tree],
      val staticInitialization: List[js.Tree],
      val topLevelExports: List[js.Tree],
      val trackedGlobalRefs: Set[String],
      val classDeps: Map[ClassName, Set[String]],
  ) extends Ordered[GeneratedClass] {
    def isEmpty: Boolean = {
      main.isEmpty &&
      staticFields.isEmpty &&
      staticInitialization.isEmpty &&
      topLevelExports.isEmpty
    }

    override def compare(that: GeneratedClass): Int = {
      val a = this.ancestorCount - that.ancestorCount
      if (a != 0) a
      else this.name.compareTo(that.name)
    }
  }

  private final class OneTimeCache[A >: Null] {
    private[this] var value: A = null
    def getOrElseUpdate(v: => A): A = {
      if (value == null)
        value = v
      value
    }
  }

  private def symbolRequirements(coreSpec: CoreSpec): SymbolRequirement = {
    import coreSpec.semantics._
    import CheckedBehavior._

    val factory = SymbolRequirement.factory("emitter")
    import factory._

    def cond(p: Boolean)(v: => SymbolRequirement): SymbolRequirement =
      if (p) v else none()

    multiple(
        cond(asInstanceOfs != Unchecked) {
          instantiateClass(ClassCastExceptionClass, StringArgConstructorName)
        },

        cond(arrayIndexOutOfBounds != Unchecked) {
          instantiateClass(ArrayIndexOutOfBoundsExceptionClass,
              StringArgConstructorName)
        },

        cond(asInstanceOfs == Fatal || arrayIndexOutOfBounds == Fatal) {
          instantiateClass(UndefinedBehaviorErrorClass,
              ThrowableArgConsructorName)
        },

        cond(moduleInit == Fatal) {
          instantiateClass(UndefinedBehaviorErrorClass,
              StringArgConstructorName)
        },

        cond(!coreSpec.esFeatures.allowBigIntsForLongs) {
          multiple(
              instanceTests(LongImpl.RuntimeLongClass),
              instantiateClass(LongImpl.RuntimeLongClass, LongImpl.AllConstructors.toList),
              callMethods(LongImpl.RuntimeLongClass, LongImpl.AllMethods.toList),
              callOnModule(LongImpl.RuntimeLongModuleClass, LongImpl.AllModuleMethods.toList)
          )
        }
    )
  }


}
