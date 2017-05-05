/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js tools             **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013-2014, LAMP/EPFL   **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package org.scalajs.core.tools.linker.backend.emitter

import scala.annotation.tailrec

import scala.collection.mutable

import org.scalajs.core.ir.{ClassKind, Position}
import org.scalajs.core.ir.Trees.JSNativeLoadSpec
import org.scalajs.core.ir.Definitions.decodeClassName

import org.scalajs.core.tools.io._
import org.scalajs.core.tools.sem._
import org.scalajs.core.tools.logging._

import org.scalajs.core.tools.javascript.{Trees => js, _}

import org.scalajs.core.tools.linker._
import org.scalajs.core.tools.linker.analyzer.SymbolRequirement
import org.scalajs.core.tools.linker.backend.{OutputMode, ModuleKind}

import GlobalRefUtils._

/** Emits a desugared JS tree to a builder */
final class Emitter private (semantics: Semantics, outputMode: OutputMode,
    moduleKind: ModuleKind, internalOptions: InternalOptions) {

  import Emitter._

  require(
      outputMode != OutputMode.ECMAScript51Global || moduleKind == ModuleKind.NoModule,
      "The ECMAScript51Global output mode is not compatible with modules")

  def this(semantics: Semantics, outputMode: OutputMode,
      moduleKind: ModuleKind) = {
    this(semantics, outputMode, moduleKind, InternalOptions())
  }

  @deprecated("Use the overload with an explicit ModuleKind.", "0.6.13")
  def this(semantics: Semantics, outputMode: OutputMode) =
    this(semantics, outputMode, ModuleKind.NoModule, InternalOptions())

  private val knowledgeGuardian = new KnowledgeGuardian

  private val baseCoreJSLib = CoreJSLibs.lib(semantics, outputMode, moduleKind)

  private var lastMentionedDangerousGlobalRefs: Set[String] = Set.empty
  private var jsGen: JSGen = recreateJSGen()
  private var classEmitter: ClassEmitter = recreateClassEmitter()
  private var coreJSLib: VirtualJSFile = recreateCoreJSLib()

  private def recreateJSGen(): JSGen = {
    new JSGen(semantics, outputMode, internalOptions,
        lastMentionedDangerousGlobalRefs)
  }

  private def recreateClassEmitter(): ClassEmitter =
    new ClassEmitter(jsGen)

  private def recreateCoreJSLib(): VirtualJSFile = {
    if (lastMentionedDangerousGlobalRefs.isEmpty) {
      baseCoreJSLib
    } else {
      var content = {
        val reader = baseCoreJSLib.reader
        try IO.readReaderToString(reader)
        finally reader.close()
      }

      for {
        globalRef <- lastMentionedDangerousGlobalRefs
        if !globalRef.startsWith("$$")
      } {
        val replacement = jsGen.avoidClashWithGlobalRef(globalRef)
        content = content.replaceAll(raw"\$globalRef\b",
            java.util.regex.Matcher.quoteReplacement(replacement))
      }

      val result = new MemVirtualJSFile(baseCoreJSLib.path)
      result.content = content
      result
    }
  }

  private val classCaches = mutable.Map.empty[List[String], ClassCache]

  private[this] var statsClassesReused: Int = 0
  private[this] var statsClassesInvalidated: Int = 0
  private[this] var statsMethodsReused: Int = 0
  private[this] var statsMethodsInvalidated: Int = 0

  val symbolRequirements: SymbolRequirement =
    Emitter.symbolRequirements(semantics, outputMode.esLevel)

  private val needsIIFEWrapper = {
    moduleKind match {
      case ModuleKind.NoModule =>
        outputMode match {
          case OutputMode.ECMAScript51Global =>
            false
          case OutputMode.ECMAScript51Isolated | OutputMode.ECMAScript6 =>
            true
        }

      case ModuleKind.CommonJSModule =>
        false
    }
  }

  // Private API for the Closure backend (could be opened if necessary)
  private[backend] def withOptimizeBracketSelects(
      optimizeBracketSelects: Boolean): Emitter = {
    new Emitter(semantics, outputMode, moduleKind,
        internalOptions.withOptimizeBracketSelects(optimizeBracketSelects))
  }

  def emitAll(unit: LinkingUnit, builder: JSFileBuilder,
      logger: Logger): Unit = {
    emitInternal(unit, builder, logger) {
      if (needsIIFEWrapper)
        builder.addLine("(function(){")

      builder.addLine("'use strict';")
      builder.addFile(coreJSLib)
    } {
      if (needsIIFEWrapper)
        builder.addLine("}).call(this);")
    }
  }

  def emitCustomHeader(customHeader: String, builder: JSFileBuilder): Unit =
    emitLines(customHeader, builder)

  /** Emits everything but the core JS lib to the builder, and returns the
   *  core JS lib.
   *
   *  This is special for the Closure back-end.
   */
  private[backend] def emitForClosure(unit: LinkingUnit, builder: JSTreeBuilder,
      logger: Logger): VirtualJSFile = {
    emitInternal(unit, builder, logger)(())(())
    coreJSLib
  }

  def emitInternal(unit: LinkingUnit, builder: JSTreeBuilder, logger: Logger)(
      emitPrelude: => Unit)(
      emitPostlude: => Unit): Unit = {
    startRun(unit)
    try {
      val orderedClasses = unit.classDefs.sortWith(compareClasses)
      val generatedClasses =
        genAllClasses(orderedClasses, logger, secondAttempt = false)

      emitPrelude

      emitModuleImports(orderedClasses, builder, logger)

      /* Emit all the classes, in the appropriate order:
       *
       * - First, all class definitions, which depend on nothing but their
       *   superclasses.
       * - Second, all static field definitions, which depend on nothing,
       *   except those of type Long which need to instantiate RuntimeLong.
       * - Third, all static initializers, which in the worst case can observe
       *   some "zero" state of other static field definitions, but must not
       *   observe a *non-initialized* (undefined) state.
       * - Finally, all the exports, during which some JS class creation can
       *   happen, causing JS static initializers to run. Those also must not
       *   observe a non-initialized state of other static fields.
       */

      def emitJSTrees(trees: List[js.Tree]): Unit =
        trees.foreach(builder.addJSTree(_))

      for (generatedClass <- generatedClasses)
        emitJSTrees(generatedClass.main)

      for (generatedClass <- generatedClasses)
        emitJSTrees(generatedClass.staticFields)

      for (generatedClass <- generatedClasses)
        emitJSTrees(generatedClass.staticInitialization)

      for (generatedClass <- generatedClasses)
        emitJSTrees(generatedClass.classExports)

      // Emit the module initializers

      for (moduleInitializer <- unit.moduleInitializers)
        emitModuleInitializer(moduleInitializer, builder)

      emitPostlude
    } finally {
      endRun(logger)
    }
  }

  private def emitModuleImports(orderedClasses: List[LinkedClass],
      builder: JSTreeBuilder, logger: Logger): Unit = {
    moduleKind match {
      case ModuleKind.NoModule =>
        var importsFound: Boolean = false

        for (classDef <- orderedClasses) {
          classDef.jsNativeLoadSpec match {
            case Some(JSNativeLoadSpec.Import(module, _)) =>
              val displayName = decodeClassName(classDef.encodedName)
              logger.error(s"$displayName needs to be imported from module " +
                  s"'$module' but module support is disabled.")
              importsFound = true

            case _ =>
              // ok
          }
        }

        if (importsFound) {
          sys.error("There were module imports, but module support is " +
              "disabled.\nTo enable module support, set scalaJSModuleKind := " +
              "ModuleKind.CommonJSModule.")
        }

      case ModuleKind.CommonJSModule =>
        val encounteredModuleNames = mutable.Set.empty[String]
        for (classDef <- orderedClasses) {
          classDef.jsNativeLoadSpec match {
            case None =>
            case Some(JSNativeLoadSpec.Global(_)) =>

            case Some(JSNativeLoadSpec.Import(module, _)) =>
              if (encounteredModuleNames.add(module)) {
                implicit val pos = classDef.pos
                val rhs = js.Apply(js.VarRef(js.Ident("require")),
                    List(js.StringLiteral(module)))
                val lhs = jsGen.envModuleField(module)
                val decl = jsGen.genLet(lhs.ident, mutable = false, rhs)
                builder.addJSTree(decl)
              }
          }
        }
    }
  }

  def emitCustomFooter(customFooter: String, builder: JSFileBuilder): Unit =
    emitLines(customFooter, builder)

  private def compareClasses(lhs: LinkedClass, rhs: LinkedClass) = {
    val lhsAC = lhs.ancestors.size
    val rhsAC = rhs.ancestors.size
    if (lhsAC != rhsAC) lhsAC < rhsAC
    else lhs.encodedName.compareTo(rhs.encodedName) < 0
  }

  private def startRun(unit: LinkingUnit): Unit = {
    statsClassesReused = 0
    statsClassesInvalidated = 0
    statsMethodsReused = 0
    statsMethodsInvalidated = 0

    val invalidateAll = knowledgeGuardian.update(unit)
    if (invalidateAll)
      classCaches.clear()

    classCaches.valuesIterator.foreach(_.startRun())
  }

  private def endRun(logger: Logger): Unit = {
    logger.debug(
        s"Emitter: Class tree cache stats: reused: $statsClassesReused -- "+
        s"invalidated: $statsClassesInvalidated")
    logger.debug(
        s"Emitter: Method tree cache stats: resued: $statsMethodsReused -- "+
        s"invalidated: $statsMethodsInvalidated")
    classCaches.retain((_, c) => c.cleanAfterRun())
  }

  /** Generates all the desugared classes.
   *
   *  If, at the end of the process, the set of accessed dangerous globals has
   *  changed, invalidate *everything* and start over. If at first you don't
   *  succeed, ...
   */
  @tailrec
  private def genAllClasses(orderedClasses: List[LinkedClass], logger: Logger,
      secondAttempt: Boolean): List[GeneratedClass] = {
    var mentionedDangerousGlobalRefs: Set[String] = Set.empty
    val generatedClasses = for (linkedClass <- orderedClasses) yield {
      val generatedClass = genClass(linkedClass)
      mentionedDangerousGlobalRefs = unionPreserveEmpty(
          mentionedDangerousGlobalRefs,
          generatedClass.mentionedDangerousGlobalRefs)
      generatedClass
    }

    if (mentionedDangerousGlobalRefs == lastMentionedDangerousGlobalRefs) {
      generatedClasses
    } else {
      assert(!secondAttempt,
          "Uh oh! The second attempt gave a different set of dangerous " +
          "global refs than the first one.")

      logger.debug(
          "Emitter: The set of dangerous global refs has changed. "+
          "Going to re-generate the world.")

      lastMentionedDangerousGlobalRefs = mentionedDangerousGlobalRefs
      jsGen = recreateJSGen()
      classEmitter = recreateClassEmitter()
      coreJSLib = recreateCoreJSLib()
      classCaches.clear()
      genAllClasses(orderedClasses, logger, secondAttempt = true)
    }
  }

  private def genClass(linkedClass: LinkedClass): GeneratedClass = {
    val className = linkedClass.encodedName
    val classCache = getClassCache(linkedClass.ancestors)
    val classTreeCache = classCache.getCache(linkedClass.version)
    val kind = linkedClass.kind

    // Global ref management

    var mentionedGlobalRefs: Set[String] = Set.empty

    def addGlobalRefs(globalRefs: Set[String]): Unit =
      mentionedGlobalRefs = unionPreserveEmpty(globalRefs, mentionedGlobalRefs)

    // Main part

    var main: List[js.Tree] = Nil

    def addToMainBase(tree: js.Tree): Unit = main ::= tree

    def addToMain(treeWithGlobals: WithGlobals[js.Tree]): Unit = {
      addToMainBase(treeWithGlobals.value)
      addGlobalRefs(treeWithGlobals.globalVarNames)
    }

    // Static methods
    for (m <- linkedClass.staticMethods) {
      val methodCache = classCache.getStaticCache(m.info.encodedName)

      addToMain(methodCache.getOrElseUpdate(m.version,
          classEmitter.genMethod(className, m.tree)(methodCache)))
    }

    // Class definition
    if (linkedClass.hasInstances && kind.isAnyScalaJSDefinedClass) {
      val ctor = classTreeCache.constructor.getOrElseUpdate(
          classEmitter.genConstructor(linkedClass)(classCache))

      // Normal methods
      val memberMethods = for (m <- linkedClass.memberMethods) yield {
        val methodCache = classCache.getMethodCache(m.info.encodedName)

        methodCache.getOrElseUpdate(m.version,
            classEmitter.genMethod(className, m.tree)(methodCache))
      }

      // Exported Members
      val exportedMembers = classTreeCache.exportedMembers.getOrElseUpdate(
          classEmitter.genExportedMembers(linkedClass)(classCache))

      addToMain(classEmitter.buildClass(linkedClass, ctor, memberMethods,
          exportedMembers)(classCache))
    } else if (kind == ClassKind.Interface) {
      // Default methods
      for (m <- linkedClass.memberMethods) yield {
        val methodCache = classCache.getMethodCache(m.info.encodedName)
        addToMain(methodCache.getOrElseUpdate(m.version,
            classEmitter.genDefaultMethod(className, m.tree)(methodCache)))
      }
    }

    if (classEmitter.needInstanceTests(linkedClass)) {
      addToMainBase(classTreeCache.instanceTests.getOrElseUpdate(js.Block(
          classEmitter.genInstanceTests(linkedClass),
          classEmitter.genArrayInstanceTests(linkedClass)
      )(linkedClass.pos)))
    }

    if (linkedClass.hasRuntimeTypeInfo) {
      addToMainBase(classTreeCache.typeData.getOrElseUpdate(
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

    // Class exports

    val classExports = if (linkedClass.classExports.isEmpty) {
      Nil
    } else {
      val treeWithGlobals = classTreeCache.classExports.getOrElseUpdate(
          classEmitter.genClassExports(linkedClass)(classCache))
      addGlobalRefs(treeWithGlobals.globalVarNames)
      treeWithGlobals.value
    }

    // Build the result

    new GeneratedClass(
        main.reverse,
        staticFields,
        staticInitialization,
        classExports,
        mentionedGlobalRefs,
        keepOnlyDangerousGlobalRefs(mentionedGlobalRefs)(outputMode)
    )
  }

  /** Emits an [[EntryPoint]].
   *
   *  This is done at the very end of the emitted module/script.
   */
  private def emitModuleInitializer(moduleInitializer: ModuleInitializer,
      builder: JSTreeBuilder): Unit = {
    builder.addJSTree(classEmitter.genModuleInitializer(moduleInitializer))
  }

  // Helpers

  private def getClassTreeCache(linkedClass: LinkedClass): DesugaredClassCache =
    getClassCache(linkedClass.ancestors).getCache(linkedClass.version)

  private def getClassCache(ancestors: List[String]) =
    classCaches.getOrElseUpdate(ancestors, new ClassCache)

  private def emitLines(str: String, builder: JSFileBuilder): Unit = {
    @tailrec def emitNextLine(index: Int): Unit = {
      val endOfLine = str.indexOf('\n', index)
      if (endOfLine != -1) {
        builder.addLine(str.substring(index, endOfLine))
        emitNextLine(endOfLine + 1)
      } else {
        builder.addLine(str.substring(index, str.length))
      }
    }
    if (str != "")
      emitNextLine(0)
  }

  // Private API for Rhino

  private[scalajs] object rhinoAPI { // scalastyle:ignore
    /** A GlobalKnowledge that never tracks dependencies. This can be used in
     *  cases where we do not use any cache, which is what `genClassDef()` in
     *  this class does.
     */
    private val globalKnowledge: GlobalKnowledge =
      new knowledgeGuardian.KnowledgeAccessor {}

    def initialize(linkingUnit: LinkingUnit): Unit =
      startRun(linkingUnit)

    def getHeaderFile(): org.scalajs.core.tools.io.VirtualJSFile =
      CoreJSLibs.lib(semantics, outputMode, moduleKind)

    def genClassDef(linkedClass: LinkedClass): js.Tree =
      classEmitter.genClassDefForRhino(linkedClass)(globalKnowledge)

    def genModuleInitializers(linkingUnit: LinkingUnit): js.Tree = {
      val genModuleInitializers =
        linkingUnit.moduleInitializers.map(classEmitter.genModuleInitializer(_))
      js.Block(genModuleInitializers)(Position.NoPosition)
    }
  }

  // Caching

  private final class ClassCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _cache: DesugaredClassCache = null
    private[this] var _lastVersion: Option[String] = None
    private[this] var _cacheUsed = false

    private[this] val _staticCaches = mutable.Map.empty[String, MethodCache]
    private[this] val _methodCaches = mutable.Map.empty[String, MethodCache]

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
      _staticCaches.valuesIterator.foreach(_.startRun())
      _methodCaches.valuesIterator.foreach(_.startRun())
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

    def getStaticCache(encodedName: String): MethodCache =
      _staticCaches.getOrElseUpdate(encodedName, new MethodCache)

    def getMethodCache(encodedName: String): MethodCache =
      _methodCaches.getOrElseUpdate(encodedName, new MethodCache)

    def cleanAfterRun(): Boolean = {
      _staticCaches.retain((_, c) => c.cleanAfterRun())
      _methodCaches.retain((_, c) => c.cleanAfterRun())

      if (!_cacheUsed)
        invalidate()

      _staticCaches.nonEmpty || _methodCaches.nonEmpty || _cacheUsed
    }
  }

  private final class MethodCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _tree: WithGlobals[js.Tree] = null
    private[this] var _lastVersion: Option[String] = None
    private[this] var _cacheUsed = false

    override def invalidate(): Unit = {
      super.invalidate()
      _tree = null
      _lastVersion = None
    }

    def startRun(): Unit = _cacheUsed = false

    def getOrElseUpdate(version: Option[String],
        v: => WithGlobals[js.Tree]): WithGlobals[js.Tree] = {
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
}

// The only reason this is not private is that Rhino needs it
private[scalajs] object Emitter {
  private final class DesugaredClassCache {
    val constructor = new OneTimeCache[WithGlobals[js.Tree]]
    val exportedMembers = new OneTimeCache[WithGlobals[js.Tree]]
    val instanceTests = new OneTimeCache[js.Tree]
    val typeData = new OneTimeCache[js.Tree]
    val setTypeData = new OneTimeCache[js.Tree]
    val moduleAccessor = new OneTimeCache[js.Tree]
    val staticFields = new OneTimeCache[List[js.Tree]]
    val classExports = new OneTimeCache[WithGlobals[List[js.Tree]]]
  }

  private final class GeneratedClass(
      val main: List[js.Tree],
      val staticFields: List[js.Tree],
      val staticInitialization: List[js.Tree],
      val classExports: List[js.Tree],
      val mentionedGlobalRefs: Set[String],
      val mentionedDangerousGlobalRefs: Set[String]
  )

  private final class OneTimeCache[A >: Null] {
    private[this] var value: A = null
    def getOrElseUpdate(v: => A): A = {
      if (value == null)
        value = v
      value
    }
  }

  // The only reason this is not private is that Rhino needs it
  private[scalajs] def symbolRequirements(semantics: Semantics,
      esLevel: ESLevel): SymbolRequirement = {
    import semantics._
    import CheckedBehavior._

    val factory = SymbolRequirement.factory("emitter")
    import factory._

    def cond(p: Boolean)(v: => SymbolRequirement): SymbolRequirement =
      if (p) v else none()

    multiple(
        instantiateClass("O", "init___"),
        classData("O"),

        instantiateClass("jl_CloneNotSupportedException", "init___"),

        cond(asInstanceOfs != Unchecked) {
          instantiateClass("jl_ClassCastException", "init___T")
        },

        cond(arrayIndexOutOfBounds != Unchecked) {
          instantiateClass("jl_ArrayIndexOutOfBoundsException", "init___T")
        },

        cond(asInstanceOfs == Fatal || arrayIndexOutOfBounds == Fatal) {
          instantiateClass("sjsr_UndefinedBehaviorError", "init___jl_Throwable")
        },

        cond(moduleInit == Fatal) {
          instantiateClass("sjsr_UndefinedBehaviorError", "init___T")
        },

        instantiateClass("jl_Class", "init___jl_ScalaJSClassData"),

        callOnModule("jl_Double$", "compare__D__D__I"),
        callOnModule("sjsr_RuntimeString$", "hashCode__T__I"),

        instanceTests(LongImpl.RuntimeLongClass),
        instantiateClass(LongImpl.RuntimeLongClass, LongImpl.AllConstructors),
        callMethods(LongImpl.RuntimeLongClass, LongImpl.AllMethods),

        callOnModule(LongImpl.RuntimeLongModuleClass, LongImpl.AllModuleMethods),

        cond(semantics.strictFloats && esLevel == ESLevel.ES5) {
          callOnModule("sjsr_package$", "froundPolyfill__D__D")
        },
        callOnModule("sjsr_Bits$", "numberHashCode__D__I")
    )
  }


}
