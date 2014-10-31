/* Scala.js compiler
 * Copyright 2013 LAMP/EPFL
 * @author  Sébastien Doeraene
 */

package scala.scalajs.compiler

import scala.language.implicitConversions

import scala.annotation.switch

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

import scala.tools.nsc._

import scala.annotation.tailrec

import scala.scalajs.ir
import ir.{Trees => js, Types => jstpe, ClassKind}

import util.ScopedVar
import ScopedVar.withScopedVars

/** Generate JavaScript code and output it to disk
 *
 *  @author Sébastien Doeraene
 */
abstract class GenJSCode extends plugins.PluginComponent
                            with TypeKinds
                            with JSEncoding
                            with GenJSExports
                            with ClassInfos
                            with GenJSFiles
                            with Compat210Component {

  val jsAddons: JSGlobalAddons {
    val global: GenJSCode.this.global.type
  }

  val scalaJSOpts: ScalaJSOptions

  import global._
  import jsAddons._
  import rootMirror._
  import definitions._
  import jsDefinitions._
  import JSTreeExtractors._

  import treeInfo.hasSynthCaseSymbol

  import platform.isMaybeBoxed

  val phaseName = "jscode"

  /** testing: this will be called when ASTs are generated */
  def generatedJSAST(clDefs: List[js.Tree]): Unit

  /** Implicit conversion from nsc Position to ir.Position. */
  implicit def pos2irPos(pos: Position): ir.Position = {
    if (pos == NoPosition) ir.Position.NoPosition
    else {
      val source = pos2irPosCache.toIRSource(pos.source)
      // nsc positions are 1-based but IR positions are 0-based
      ir.Position(source, pos.line-1, pos.column-1)
    }
  }

  private[this] object pos2irPosCache {
    import scala.reflect.internal.util._

    private[this] var lastNscSource: SourceFile = null
    private[this] var lastIRSource: ir.Position.SourceFile = null

    def toIRSource(nscSource: SourceFile): ir.Position.SourceFile = {
      if (nscSource != lastNscSource) {
        lastIRSource = convert(nscSource)
        lastNscSource = nscSource
      }
      lastIRSource
    }

    private[this] def convert(nscSource: SourceFile): ir.Position.SourceFile = {
      nscSource.file.file match {
        case null =>
          new java.net.URI(
              "virtualfile",       // Pseudo-Scheme
              nscSource.file.path, // Scheme specific part
              null                 // Fragment
          )
        case file =>
          val srcURI = file.toURI
          def matches(pat: java.net.URI) = pat.relativize(srcURI) != srcURI

          scalaJSOpts.sourceURIMaps.collectFirst {
            case ScalaJSOptions.URIMap(from, to) if matches(from) =>
              val relURI = from.relativize(srcURI)
              to.fold(relURI)(_.resolve(relURI))
          } getOrElse srcURI
      }
    }

    def clear(): Unit = {
      lastNscSource = null
      lastIRSource = null
    }
  }

  /** Materialize implicitly an ir.Position from an implicit nsc Position. */
  implicit def implicitPos2irPos(implicit pos: Position): ir.Position = pos

  override def newPhase(p: Phase) = new JSCodePhase(p)

  private object jsnme {
    val arg_outer = newTermName("arg$outer")
    val newString = newTermName("newString")

    val Zero      = newTermName("Zero")
    val One       = newTermName("One")
    val notEquals = newTermName("notEquals")

    val fromByte   = newTermName("fromByte")
    val fromShort  = newTermName("fromShort")
    val fromChar   = newTermName("fromChar")
    val fromInt    = newTermName("fromInt")
    val fromFloat  = newTermName("fromFloat")
    val fromDouble = newTermName("fromDouble")

    val toByte   = newTermName("toByte")
    val toShort  = newTermName("toShort")
    val toChar   = newTermName("toChar")
    val toInt    = newTermName("toInt")
    val toFloat  = newTermName("toFloat")
    val toDouble = newTermName("toDouble")
  }

  class JSCodePhase(prev: Phase) extends StdPhase(prev) with JSExportsPhase {

    override def name = phaseName
    override def description = "Generate JavaScript code from ASTs"
    override def erasedTypes = true

    // Some state --------------------------------------------------------------

    val currentClassSym             = new ScopedVar[Symbol]
    val currentClassInfoBuilder     = new ScopedVar[ClassInfoBuilder]
    val currentMethodSym            = new ScopedVar[Symbol]
    val currentMethodInfoBuilder    = new ScopedVar[MethodInfoBuilder]
    val methodTailJumpThisSym       = new ScopedVar[Symbol](NoSymbol)
    val methodTailJumpLabelSym      = new ScopedVar[Symbol]
    val methodTailJumpFormalArgs    = new ScopedVar[List[Symbol]]
    val methodTailJumpFormalArgsSet = new ScopedVar[Set[Symbol]]
    val mutableLocalVars            = new ScopedVar[mutable.Set[Symbol]]
    val mutatedLocalVars            = new ScopedVar[mutable.Set[Symbol]]
    val paramAccessorLocals         = new ScopedVar(Map.empty[Symbol, js.ParamDef])

    var isModuleInitialized: Boolean = false // see genApply for super calls

    def currentClassType = encodeClassType(currentClassSym)

    val tryingToGenMethodAsJSFunction = new ScopedVar[Boolean](false)
    class CancelGenMethodAsJSFunction(message: String)
        extends Throwable(message) with scala.util.control.ControlThrowable

    // Rewriting of anonymous function classes ---------------------------------

    private val translatedAnonFunctions =
      mutable.Map.empty[Symbol,
        (/*ctor args:*/ List[js.Tree] => /*instance:*/ js.Tree, ClassInfoBuilder)]
    private val instantiatedAnonFunctions =
      mutable.Set.empty[Symbol]
    private val undefinedDefaultParams =
      mutable.Set.empty[Symbol]

    // Top-level apply ---------------------------------------------------------

    override def run() {
      scalaPrimitives.init()
      jsPrimitives.init()
      super.run()
    }

    /** Generates the Scala.js IR for a compilation unit
     *  This method iterates over all the class and interface definitions
     *  found in the compilation unit and emits their IR (.sjsir).
     *
     *  Some classes are never actually emitted:
     *  - Classes representing primitive types
     *  - The scala.Array class
     *  - Implementation classes for raw JS traits
     *
     *  Some classes representing anonymous functions are not actually emitted.
     *  Instead, a temporary representation of their `apply` method is built
     *  and recorded, so that it can be inlined as a JavaScript anonymous
     *  function in the method that instantiates it.
     *
     *  Other ClassDefs are emitted according to their nature:
     *  * Raw JS type (<: js.Any) -> `genRawJSClassData()`
     *  * Interface               -> `genInterface()`
     *  * Implementation class    -> `genImplClass()`
     *  * Hijacked boxed class    -> `genHijackedBoxedClassData()`
     *  * Normal class            -> `genClass()`
     */
    override def apply(cunit: CompilationUnit) {
      try {
        val generatedClasses = ListBuffer.empty[(Symbol, js.ClassDef, ClassInfoBuilder)]

        def collectClassDefs(tree: Tree): List[ClassDef] = {
          tree match {
            case EmptyTree => Nil
            case PackageDef(_, stats) => stats flatMap collectClassDefs
            case cd: ClassDef => cd :: Nil
          }
        }
        val allClassDefs = collectClassDefs(cunit.body)

        /* First gen and record lambdas for js.FunctionN and js.ThisFunctionN.
         * Since they are SAMs, there cannot be dependencies within this set,
         * and hence we are sure we can record them before they are used,
         * which is critical for these.
         */
        val nonRawJSFunctionDefs = allClassDefs filterNot { cd =>
          if (isRawJSFunctionDef(cd.symbol)) {
            genAndRecordRawJSFunctionClass(cd)
            true
          } else {
            false
          }
        }

        /* Then try to gen and record lambdas for scala.FunctionN.
         * These may fail, and sometimes because of dependencies. Since there
         * appears to be more forward dependencies than backward dependencies
         * (at least for non-nested lambdas, which we cannot translate anyway),
         * we process class defs in reverse order here.
         */
        val fullClassDefs = (nonRawJSFunctionDefs.reverse filterNot { cd =>
          cd.symbol.isAnonymousFunction && tryGenAndRecordAnonFunctionClass(cd)
        }).reverse

        /* Finally, we emit true code for the remaining class defs. */
        for (cd <- fullClassDefs) {
          val sym = cd.symbol
          implicit val pos = sym.pos

          /* Do not actually emit code for primitive types nor scala.Array. */
          val isPrimitive =
            isPrimitiveValueClass(sym) || (sym == ArrayClass)

          /* Similarly, do not emit code for impl classes of raw JS traits. */
          val isRawJSImplClass =
            sym.isImplClass && isRawJSType(
                sym.owner.info.decl(sym.name.dropRight(nme.IMPL_CLASS_SUFFIX.length)).tpe)

          if (!isPrimitive && !isRawJSImplClass) {
            withScopedVars(
                currentClassInfoBuilder := new ClassInfoBuilder(sym.asClass),
                currentClassSym         := sym
            ) {
              val tree = if (isRawJSType(sym.tpe)) {
                assert(!isRawJSFunctionDef(sym),
                    s"Raw JS function def should have been recorded: $cd")
                genRawJSClassData(cd)
              } else if (sym.isInterface) {
                genInterface(cd)
              } else if (sym.isImplClass) {
                genImplClass(cd)
              } else if (isHijackedBoxedClass(sym)) {
                genHijackedBoxedClassData(cd)
              } else {
                genClass(cd)
              }
              generatedClasses += ((sym, tree, currentClassInfoBuilder.get))
            }
          }
        }

        val clDefs = generatedClasses.map(_._2).toList
        generatedJSAST(clDefs)

        for ((sym, tree, infoBuilder) <- generatedClasses) {
          genIRFile(cunit, sym, tree, infoBuilder.result())
        }
      } finally {
        translatedAnonFunctions.clear()
        instantiatedAnonFunctions.clear()
        undefinedDefaultParams.clear()
        pos2irPosCache.clear()
      }
    }

    // Generate a class --------------------------------------------------------

    /** Gen the IR ClassDef for a class definition (maybe a module class).
     */
    def genClass(cd: ClassDef): js.ClassDef = {
      val ClassDef(mods, name, _, impl) = cd
      val sym = cd.symbol
      implicit val pos = sym.pos

      assert(!sym.isInterface && !sym.isImplClass,
          "genClass() must be called only for normal classes: "+sym)
      assert(sym.superClass != NoSymbol, sym)

      val classIdent = encodeClassFullNameIdent(sym)

      // Optimizer hints

      def isStdLibClassWithAdHocInlineAnnot(sym: Symbol): Boolean = {
        val fullName = sym.fullName
        (fullName.startsWith("scala.Tuple") && !fullName.endsWith("$")) ||
        (fullName.startsWith("scala.collection.mutable.ArrayOps$of"))
      }

      if (sym.hasAnnotation(InlineAnnotationClass) ||
          (sym.isAnonymousFunction && !sym.isSubClass(PartialFunctionClass)) ||
          isStdLibClassWithAdHocInlineAnnot(sym))
        currentClassInfoBuilder.optimizerHints =
          currentClassInfoBuilder.optimizerHints.copy(hasInlineAnnot = true)

      // Generate members (constructor + methods)

      val generatedMembers = new ListBuffer[js.Tree]
      val exportedSymbols = new ListBuffer[Symbol]

      generatedMembers ++= genClassFields(cd)

      def gen(tree: Tree): Unit = {
        tree match {
          case EmptyTree => ()
          case Template(_, _, body) => body foreach gen

          case ValDef(mods, name, tpt, rhs) =>
            () // fields are added via genClassFields()

          case dd: DefDef =>
            val sym = dd.symbol

            val isExport = jsInterop.isExport(sym)
            val isNamedExport = isExport && sym.annotations.exists(
                _.symbol == JSExportNamedAnnotation)

            if (isNamedExport)
              generatedMembers += genNamedExporterDef(dd)
            else
              generatedMembers ++= genMethod(dd)

            if (isExport) {
              // We add symbols that we have to export here. This way we also
              // get inherited stuff that is implemented in this class.
              exportedSymbols += sym
            }

          case _ => abort("Illegal tree in gen of genClass(): " + tree)
        }
      }

      gen(impl)

      // Create method info builder for exported stuff
      val exports = withScopedVars(
        currentMethodInfoBuilder := currentClassInfoBuilder.addMethod(
            dceExportName + classIdent.name, isExported = true)
      ) {
        // Generate the exported members
        val memberExports = genMemberExports(sym, exportedSymbols.toList)

        // Generate exported constructors or accessors
        val exportedConstructorsOrAccessors =
          if (isStaticModule(sym)) genModuleAccessorExports(sym)
          else genConstructorExports(sym)
        if (exportedConstructorsOrAccessors.nonEmpty)
          currentClassInfoBuilder.isExported = true

        memberExports ++ exportedConstructorsOrAccessors
      }

      // Generate the reflective call proxies (where required)
      val reflProxies = genReflCallProxies(sym)

      // The complete class definition
      val classDefinition = js.ClassDef(
          classIdent,
          if (sym.isModuleClass) ClassKind.ModuleClass else ClassKind.Class,
          Some(encodeClassFullNameIdent(sym.superClass)),
          sym.ancestors.map(encodeClassFullNameIdent),
          generatedMembers.toList ++ exports ++ reflProxies)

      classDefinition
    }

    // Generate the class data of a raw JS class -------------------------------

    /** Gen the IR ClassDef for a raw JS class or trait.
     */
    def genRawJSClassData(cd: ClassDef): js.ClassDef = {
      val sym = cd.symbol
      implicit val pos = sym.pos

      // Check that RawJS type is not exported
      for (exp <- jsInterop.exportsOf(sym)) {
        currentUnit.error(exp.pos,
            "You may not export a class extending js.Any")
      }

      val classIdent = encodeClassFullNameIdent(sym)
      js.ClassDef(classIdent, ClassKind.RawJSType, None, Nil, Nil)
    }

    // Generate the class data of a hijacked boxed class -----------------------

    /** Gen the IR ClassDef for a hijacked boxed class.
     */
    def genHijackedBoxedClassData(cd: ClassDef): js.ClassDef = {
      val sym = cd.symbol
      implicit val pos = sym.pos
      val classIdent = encodeClassFullNameIdent(sym)
      js.ClassDef(classIdent, ClassKind.HijackedClass, None,
          sym.ancestors.map(encodeClassFullNameIdent), Nil)
    }

    // Generate an interface ---------------------------------------------------

    /** Gen the IR ClassDef for an interface definition.
     */
    def genInterface(cd: ClassDef): js.ClassDef = {
      val sym = cd.symbol
      implicit val pos = sym.pos

      val classIdent = encodeClassFullNameIdent(sym)

      // fill in class info builder
      def gen(tree: Tree) {
        tree match {
          case EmptyTree => ()
          case Template(_, _, body) => body foreach gen
          case dd: DefDef =>
            currentClassInfoBuilder.addMethod(
                encodeMethodName(dd.symbol), isAbstract = true)
          case _ => abort("Illegal tree in gen of genInterface(): " + tree)
        }
      }
      gen(cd.impl)

      // Check that interface/trait is not exported
      for (exp <- jsInterop.exportsOf(sym)) {
        currentUnit.error(exp.pos, "You may not export a trait")
      }

      js.ClassDef(classIdent, ClassKind.Interface, None,
          sym.ancestors.map(encodeClassFullNameIdent), Nil)
    }

    // Generate an implementation class of a trait -----------------------------

    /** Gen the IR ClassDef for an implementation class (of a trait).
     */
    def genImplClass(cd: ClassDef): js.ClassDef = {
      val ClassDef(mods, name, _, impl) = cd
      val sym = cd.symbol
      implicit val pos = sym.pos

      def gen(tree: Tree): List[js.MethodDef] = {
        tree match {
          case EmptyTree => Nil
          case Template(_, _, body) => body.flatMap(gen)

          case dd: DefDef =>
            val m = genMethod(dd)
            m.toList

          case _ => abort("Illegal tree in gen of genImplClass(): " + tree)
        }
      }
      val generatedMethods = gen(impl)

      js.ClassDef(encodeClassFullNameIdent(sym), ClassKind.TraitImpl,
          None, Nil, generatedMethods)
    }

    // Generate the fields of a class ------------------------------------------

    /** Gen definitions for the fields of a class.
     *  The fields are initialized with the zero of their types.
     */
    def genClassFields(cd: ClassDef): List[js.VarDef] = withScopedVars(
        currentMethodInfoBuilder :=
          currentClassInfoBuilder.addMethod("__init__")
    ) {
      // Non-method term members are fields, except for module members.
      (for {
        f <- currentClassSym.info.decls
        if !f.isMethod && f.isTerm && !f.isModule
      } yield {
        implicit val pos = f.pos
        js.VarDef(encodeFieldSym(f), toIRType(f.tpe),
            mutable = f.isMutable, genZeroOf(f.tpe))
      }).toList
    }

    // Generate a method -------------------------------------------------------

    def genMethod(dd: DefDef): Option[js.MethodDef] = withNewLocalNameScope {
      genMethodWithInfoBuilder(dd).map(_._1)
    }

    /** Gen JS code for a method definition in a class or in an impl class.
     *  On the JS side, method names are mangled to encode the full signature
     *  of the Scala method, as described in `JSEncoding`, to support
     *  overloading.
     *
     *  Some methods are not emitted at all:
     *  * Primitives, since they are never actually called
     *  * Abstract methods
     *  * Trivial constructors, which only call their super constructor, with
     *    the same signature, and the same arguments. The JVM needs these
     *    constructors, but not JavaScript. Since there are lots of them, we
     *    take the trouble of recognizing and removing them.
     *
     *  Constructors are emitted by generating their body as a statement, then
     *  return `this`.
     *
     *  Other (normal) methods are emitted with `genMethodBody()`.
     */
    def genMethodWithInfoBuilder(
        dd: DefDef): Option[(js.MethodDef, MethodInfoBuilder)] = {

      implicit val pos = dd.pos
      val DefDef(mods, name, _, vparamss, _, rhs) = dd
      val sym = dd.symbol

      isModuleInitialized = false

      val result = withScopedVars(
          currentMethodSym            := sym,
          methodTailJumpThisSym       := NoSymbol,
          methodTailJumpLabelSym      := NoSymbol,
          methodTailJumpFormalArgs    := Nil,
          methodTailJumpFormalArgsSet := Set.empty
      ) {
        assert(vparamss.isEmpty || vparamss.tail.isEmpty,
            "Malformed parameter list: " + vparamss)
        val params = if (vparamss.isEmpty) Nil else vparamss.head map (_.symbol)

        assert(!sym.owner.isInterface,
            "genMethod() must not be called for methods in interfaces: "+sym)

        val methodIdent = encodeMethodSym(sym)

        def createInfoBuilder(isAbstract: Boolean = false) = {
          currentClassInfoBuilder.addMethod(methodIdent.name,
              isAbstract = isAbstract,
              isExported = sym.isClassConstructor &&
                jsInterop.exportsOf(sym).nonEmpty)
        }

        if (scalaPrimitives.isPrimitive(sym)) {
          None
        } else if (sym.isDeferred) {
          createInfoBuilder(isAbstract = true)
          None
        } else if (isTrivialConstructor(sym, params, rhs)) {
          createInfoBuilder().callsMethod(sym.owner.superClass, methodIdent)
          None
        } else {
          withScopedVars(
              currentMethodInfoBuilder := createInfoBuilder(),
              mutableLocalVars := mutable.Set.empty,
              mutatedLocalVars := mutable.Set.empty
          ) {
            def shouldMarkInline = {
              sym.hasAnnotation(InlineAnnotationClass) ||
              sym.name.startsWith(nme.ANON_FUN_NAME)
            }
            currentMethodInfoBuilder.optimizerHints =
              currentMethodInfoBuilder.optimizerHints.copy(
                  isAccessor = sym.isAccessor,
                  hasInlineAnnot = shouldMarkInline)

            val methodDef = {
              if (sym.isClassConstructor) {
                val jsParams = for (param <- params) yield {
                  implicit val pos = param.pos
                  js.ParamDef(encodeLocalSym(param), toIRType(param.tpe),
                      mutable = false)
                }
                js.MethodDef(methodIdent, jsParams, currentClassType,
                    js.Block(genStat(rhs), genThis()))
              } else {
                val resultIRType = toIRType(sym.tpe.resultType)
                genMethodDef(methodIdent, params, resultIRType, rhs)
              }
            }

            val methodDefWithoutUselessVars = {
              val unmutatedMutableLocalVars =
                (mutableLocalVars -- mutatedLocalVars).toSet
              if (unmutatedMutableLocalVars.isEmpty) methodDef
              else patchMutableLocalVarsAsVals(methodDef,
                  unmutatedMutableLocalVars.map(encodeLocalSym(_).name))
            }

            Some((methodDefWithoutUselessVars, currentMethodInfoBuilder.get))
          }
        }
      }

      result
    }

    private def isTrivialConstructor(sym: Symbol, params: List[Symbol],
        rhs: Tree): Boolean = {
      if (!sym.isClassConstructor) {
        false
      } else {
        rhs match {
          // Shape of a constructor that only calls super
          case Block(List(Apply(fun @ Select(_:Super, _), args)), Literal(_)) =>
            val callee = fun.symbol
            implicit val dummyPos = NoPosition

            // Does the callee have the same signature as sym
            if (encodeMethodSym(sym) == encodeMethodSym(callee)) {
              // Test whether args are trivial forwarders
              assert(args.size == params.size, "Argument count mismatch")
              params.zip(args) forall { case (param, arg) =>
                arg.symbol == param
              }
            } else {
              false
            }

          case _ => false
        }
      }
    }

    /** Patches a [[js.MethodDef]] to transform some local vars as vals.
     */
    private def patchMutableLocalVarsAsVals(methodDef: js.MethodDef,
        varNames: Set[String]): js.MethodDef = {
      val js.MethodDef(methodName, params, resultType, body) = methodDef
      val newParams = for {
        p @ js.ParamDef(name, ptpe, _) <- params
      } yield {
        if (varNames.contains(name.name)) js.ParamDef(name, ptpe, false)(p.pos)
        else p
      }
      val transformer = new ir.Transformers.Transformer {
        override def transformStat(tree: js.Tree): js.Tree =
          transform(tree, isStat = true)
        override def transformExpr(tree: js.Tree): js.Tree =
          transform(tree, isStat = false)

        private def transform(tree: js.Tree, isStat: Boolean): js.Tree = tree match {
          case js.VarDef(name, vtpe, _, rhs) if varNames.contains(name.name) =>
            assert(isStat)
            super.transformStat(js.VarDef(name, vtpe, false, rhs)(tree.pos))
          case js.VarRef(name, _) if varNames.contains(name.name) =>
            js.VarRef(name, false)(tree.tpe)(tree.pos)
          case js.Closure(thisType, params, resultType, body, captures) =>
            js.Closure(thisType, params, resultType, body,
                captures.map(transformExpr))(tree.pos)
          case _ =>
            if (isStat) super.transformStat(tree)
            else super.transformExpr(tree)
        }
      }
      val newBody =
        if (resultType == jstpe.NoType) transformer.transformStat(body)
        else transformer.transformExpr(body)
      js.MethodDef(methodName, newParams, resultType, newBody)(methodDef.pos)
    }

    /**
     * Generates reflective proxy methods for methods in sym
     *
     * Reflective calls don't depend on the return type, so it's hard to
     * generate calls without using runtime reflection to list the methods. We
     * generate a method to be used for reflective calls (without return
     * type in the name).
     *
     * There are cases where non-trivial overloads cause ambiguous situations:
     *
     * {{{
     * object A {
     *   def foo(x: Option[Int]): String
     *   def foo(x: Option[String]): Int
     * }
     * }}}
     *
     * This is completely legal code, but due to the same erased parameter
     * type of the {{{foo}}} overloads, they cannot be disambiguated in a
     * reflective call, as the exact return type is unknown at the call site.
     *
     * Cases like the upper currently fail on the JVM backend at runtime. The
     * Scala.js backend uses the following rules for selection (which will
     * also cause runtime failures):
     *
     * - If a proxy with the same signature (method name and parameters)
     *   exists in the superclass, no proxy is generated (proxy is inherited)
     * - If no proxy exists in the superclass, a proxy is generated for the
     *   first method with matching signatures.
     */
    def genReflCallProxies(sym: Symbol): List[js.MethodDef] = {
      import scala.reflect.internal.Flags

      // Flags of members we do not want to consider for reflective call proxys
      val excludedFlags = (
          Flags.BRIDGE  |
          Flags.PRIVATE |
          Flags.MACRO
      )

      /** Check if two method symbols conform in name and parameter types */
      def weakMatch(s1: Symbol)(s2: Symbol) = {
        val p1 = s1.tpe.params
        val p2 = s2.tpe.params
        s1 == s2 || // Shortcut
        s1.name == s2.name &&
        p1.size == p2.size &&
        (p1 zip p2).forall { case (s1,s2) =>
          s1.tpe =:= s2.tpe
        }
      }

      /** Check if the symbol's owner's superclass has a matching member (and
       *  therefore an existing proxy).
       */
      def superHasProxy(s: Symbol) = {
        val alts = sym.superClass.tpe.findMember(
            name = s.name,
            excludedFlags = excludedFlags,
            requiredFlags = Flags.METHOD,
            stableOnly    = false).alternatives
        alts.exists(weakMatch(s) _)
      }

      // Query candidate methods
      val methods = sym.tpe.findMembers(
          excludedFlags = excludedFlags,
          requiredFlags = Flags.METHOD)

      val candidates = methods filterNot { s =>
        s.isConstructor  ||
        superHasProxy(s) ||
        jsInterop.isExport(s)
      }

      val proxies = candidates filter {
        c => candidates.find(weakMatch(c) _).get == c
      }

      proxies.map(genReflCallProxy _).toList
    }

    /** actually generates reflective call proxy for the given method symbol */
    private def genReflCallProxy(sym: Symbol): js.MethodDef = {
      implicit val pos = sym.pos

      val proxyIdent = encodeMethodSym(sym, reflProxy = true)

      withNewLocalNameScope {
        withScopedVars(
            currentMethodInfoBuilder :=
              currentClassInfoBuilder.addMethod(proxyIdent.name)
        ) {
          val jsParams = for (param <- sym.tpe.params) yield {
            implicit val pos = param.pos
            js.ParamDef(encodeLocalSym(param), toIRType(param.tpe),
                mutable = false)
          }

          val call = genApplyMethod(genThis(), sym.owner, sym,
              jsParams.map(_.ref))
          val body = ensureBoxed(call,
              enteringPhase(currentRun.posterasurePhase)(sym.tpe.resultType))

          js.MethodDef(proxyIdent, jsParams, jstpe.AnyType, body)
        }
      }
    }

    /** Generates the MethodDef of a (non-constructor) method
     *
     *  Most normal methods are emitted straightforwardly. If the result
     *  type is Unit, then the body is emitted as a statement. Otherwise, it is
     *  emitted as an expression.
     *
     *  The additional complexity of this method handles the transformation of
     *  recursive tail calls. The `tailcalls` phase transforms them as one big
     *  LabelDef surrounding the body of the method, and label-Apply's for
     *  recursive tail calls.
     *  Here, we transform the outer LabelDef into a labeled `while (true)`
     *  loop. Label-Apply's to the LabelDef are turned into a `continue` of
     *  that loop. The body of the loop is a `js.Return()` of the body of the
     *  LabelDef (even if the return type is Unit), which will break out of
     *  the loop as necessary.
     *  In that case, the ParamDefs are marked as mutable, as well as the
     *  variable that replaces `this` (if there is one).
     */
    def genMethodDef(methodIdent: js.Ident, paramsSyms: List[Symbol],
        resultIRType: jstpe.Type, tree: Tree): js.MethodDef = {
      implicit val pos = tree.pos

      def jsParams(mutable: Boolean) = for (param <- paramsSyms) yield {
        implicit val pos = param.pos
        js.ParamDef(encodeLocalSym(param), toIRType(param.tpe), mutable)
      }

      val bodyIsStat = resultIRType == jstpe.NoType

      tree match {
        case Block(
            List(thisDef @ ValDef(_, nme.THIS, _, initialThis)),
            ld @ LabelDef(labelName, _, rhs)) =>
          // This method has tail jumps
          withScopedVars(
            (methodTailJumpLabelSym := ld.symbol) +:
            (initialThis match {
              case This(_) => Seq(
                methodTailJumpThisSym       := thisDef.symbol,
                methodTailJumpFormalArgs    := thisDef.symbol :: paramsSyms,
                methodTailJumpFormalArgsSet := paramsSyms.toSet + thisDef.symbol)
              case Ident(_) => Seq(
                methodTailJumpThisSym       := NoSymbol,
                methodTailJumpFormalArgs    := paramsSyms,
                methodTailJumpFormalArgsSet := paramsSyms.toSet)
            }): _*
          ) {
            mutableLocalVars ++= methodTailJumpFormalArgsSet
            val theLoop =
              js.While(js.BooleanLiteral(true),
                  if (bodyIsStat) js.Block(genStat(rhs), js.Return(js.Undefined()))
                  else            js.Return(genExpr(rhs)),
                  Some(js.Ident("tailCallLoop")))

            val body = if (methodTailJumpThisSym.get == NoSymbol) {
              theLoop
            } else {
              js.Block(
                  js.VarDef(encodeLocalSym(methodTailJumpThisSym),
                      currentClassType, mutable = true,
                      js.This()(currentClassType)),
                  theLoop)
            }
            js.MethodDef(methodIdent, jsParams(true), resultIRType, body)
          }

        case _ =>
          val body =
            if (bodyIsStat) genStat(tree)
            else genExpr(tree)
          js.MethodDef(methodIdent, jsParams(false), resultIRType, body)
      }
    }

    /** Gen JS code for a tree in statement position (in the IR).
     */
    def genStat(tree: Tree): js.Tree = {
      exprToStat(genStatOrExpr(tree, isStat = true))
    }

    /** Turn a JavaScript expression of type Unit into a statement */
    def exprToStat(tree: js.Tree): js.Tree = {
      /* Any JavaScript expression is also a statement, but at least we get rid
       * of some pure expressions that come from our own codegen.
       */
      implicit val pos = tree.pos
      tree match {
        case js.Block(stats :+ expr)  => js.Block(stats :+ exprToStat(expr))
        case _:js.Literal | js.This() => js.Skip()
        case js.Cast(expr, _)         => exprToStat(expr)
        case _                        => tree
      }
    }

    /** Gen JS code for a tree in expression position (in the IR).
     */
    def genExpr(tree: Tree): js.Tree = {
      val result = genStatOrExpr(tree, isStat = false)
      assert(result.tpe != jstpe.NoType,
          s"genExpr($tree) returned a tree with type NoType at pos ${tree.pos}")
      result
    }

    /** Gen JS code for a tree in statement or expression position (in the IR).
     *
     *  This is the main transformation method. Each node of the Scala AST
     *  is transformed into an equivalent portion of the JS AST.
     */
    def genStatOrExpr(tree: Tree, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos

      tree match {
        /** LabelDefs (for while and do..while loops) */
        case lblDf: LabelDef =>
          genLabelDef(lblDf)

        /** Local val or var declaration */
        case ValDef(_, name, _, rhs) =>
          /* Must have been eliminated by the tail call transform performed
           * by genMethodBody(). */
          assert(name != nme.THIS,
              s"ValDef(_, nme.THIS, _, _) found at ${tree.pos}")

          val sym = tree.symbol
          val rhsTree =
            if (rhs == EmptyTree) genZeroOf(sym.tpe)
            else genExpr(rhs)

          rhsTree match {
            case js.UndefinedParam() =>
              // This is an intermediate assignment for default params on a
              // js.Any. Add the symbol to the corresponding set to inform
              // the Ident resolver how to replace it and don't emit the symbol
              undefinedDefaultParams += sym
              js.Skip()
            case _ =>
              if (sym.isMutable)
                mutableLocalVars += sym
              js.VarDef(encodeLocalSym(sym),
                  toIRType(sym.tpe), sym.isMutable, rhsTree)
          }

        case If(cond, thenp, elsep) =>
          js.If(genExpr(cond), genStatOrExpr(thenp, isStat),
              genStatOrExpr(elsep, isStat))(toIRType(tree.tpe))

        case Return(expr) =>
          js.Return(toIRType(expr.tpe) match {
            case jstpe.NoType => js.Block(genStat(expr), js.Undefined())
            case _            => genExpr(expr)
          })

        case t: Try =>
          genTry(t, isStat)

        case Throw(expr) =>
          val ex = genExpr(expr)
          if (isMaybeJavaScriptException(expr.tpe))
            js.Throw(js.CallHelper("unwrapJavaScriptException", ex)(jstpe.AnyType))
          else
            js.Throw(ex)

        case app: Apply =>
          genApply(app, isStat)

        case app: ApplyDynamic =>
          genApplyDynamic(app)

        case This(qual) =>
          if (tree.symbol == currentClassSym.get) {
            genThis()
          } else {
            assert(tree.symbol.isModuleClass,
                "Trying to access the this of another class: " +
                "tree.symbol = " + tree.symbol +
                ", class symbol = " + currentClassSym.get +
                " compilation unit:" + currentUnit)
            genLoadModule(tree.symbol)
          }

        case Select(qualifier, selector) =>
          val sym = tree.symbol
          if (sym.isModule) {
            assert(!sym.isPackageClass, "Cannot use package as value: " + tree)
            genLoadModule(sym)
          } else if (sym.isStaticMember) {
            genStaticMember(sym)
          } else if (paramAccessorLocals contains sym) {
            paramAccessorLocals(sym).ref
          } else {
            js.Select(genExpr(qualifier), encodeFieldSym(sym),
                mutable = sym.isMutable)(toIRType(sym.tpe))
          }

        case Ident(name) =>
          val sym = tree.symbol
          if (!sym.hasPackageFlag) {
            if (sym.isModule) {
              assert(!sym.isPackageClass, "Cannot use package as value: " + tree)
              genLoadModule(sym)
            } else if (undefinedDefaultParams contains sym) {
              // This is a default parameter whose assignment was moved to
              // a local variable. Put a literal undefined param again
              js.UndefinedParam()(toIRType(sym.tpe))
            } else {
              val mutable =
                sym.isMutable || methodTailJumpFormalArgsSet.contains(sym)
              js.VarRef(encodeLocalSym(sym), mutable)(toIRType(sym.tpe))
            }
          } else {
            sys.error("Cannot use package as value: " + tree)
          }

        case Literal(value) =>
          value.tag match {
            case UnitTag =>
              js.Skip()
            case BooleanTag =>
              js.BooleanLiteral(value.booleanValue)
            case ByteTag | ShortTag | CharTag | IntTag =>
              js.IntLiteral(value.intValue)
            case LongTag =>
              // Convert literal to triplet (at compile time!)
              val (l, m, h) = JSConversions.scalaLongToTriplet(value.longValue)
              genLongModuleCall(nme.apply, js.IntLiteral(l), js.IntLiteral(m), js.IntLiteral(h))
            case FloatTag | DoubleTag =>
              js.DoubleLiteral(value.doubleValue)
            case StringTag =>
              js.StringLiteral(value.stringValue)
            case NullTag =>
              js.Null()
            case ClazzTag =>
              genClassConstant(value.typeValue)
            case EnumTag =>
              genStaticMember(value.symbolValue)
          }

        case tree: Block =>
          genBlock(tree, isStat)

        case Typed(Super(_, _), _) =>
          genThis()

        case Typed(expr, _) =>
          genExpr(expr)

        case Assign(lhs, rhs) =>
          val sym = lhs.symbol
          if (sym.isStaticMember)
            abort(s"Assignment to static member ${sym.fullName} not supported")
          val genLhs = lhs match {
            case Select(qualifier, _) =>
              js.Select(genExpr(qualifier), encodeFieldSym(sym),
                  mutable = sym.isMutable)(toIRType(sym.tpe))
            case _ =>
              val mutable =
                sym.isMutable || methodTailJumpFormalArgsSet.contains(sym)
              if (mutable)
                mutatedLocalVars += sym
              js.VarRef(encodeLocalSym(sym), mutable)(toIRType(sym.tpe))
          }
          js.Assign(genLhs, genExpr(rhs))

        /** Array constructor */
        case av: ArrayValue =>
          genArrayValue(av)

        /** A Match reaching the backend is supposed to be optimized as a switch */
        case mtch: Match =>
          genMatch(mtch, isStat)

        /** Anonymous function (only with -Ydelambdafy:method) */
        case fun: Function =>
          genAnonFunction(fun)

        case EmptyTree =>
          js.Skip()

        case _ =>
          abort("Unexpected tree in genExpr: " +
              tree + "/" + tree.getClass + " at: " + tree.pos)
      }
    } // end of GenJSCode.genExpr()

    /** Gen JS this of the current class.
     *  Normally encoded straightforwardly as a JS this.
     *  But must be replaced by the tail-jump-this local variable if there
     *  is one.
     */
    private def genThis()(implicit pos: Position): js.Tree = {
      if (methodTailJumpThisSym.get != NoSymbol) {
        js.VarRef(
          encodeLocalSym(methodTailJumpThisSym),
          mutable = true)(currentClassType)
      } else {
        if (tryingToGenMethodAsJSFunction)
          throw new CancelGenMethodAsJSFunction(
              "Trying to generate `this` inside the body")
        js.This()(currentClassType)
      }
    }

    /** Gen JS code for LabelDef
     *  The only LabelDefs that can reach here are the desugaring of
     *  while and do..while loops. All other LabelDefs (for tail calls or
     *  matches) are caught upstream and transformed in ad hoc ways.
     *
     *  So here we recognize all the possible forms of trees that can result
     *  of while or do..while loops, and we reconstruct the loop for emission
     *  to JS.
     */
    def genLabelDef(tree: LabelDef): js.Tree = {
      implicit val pos = tree.pos
      val sym = tree.symbol

      tree match {
        // while (cond) { body }
        case LabelDef(lname, Nil,
            If(cond,
                Block(bodyStats, Apply(target @ Ident(lname2), Nil)),
                Literal(_))) if (target.symbol == sym) =>
          js.While(genExpr(cond), js.Block(bodyStats map genStat))

        // while (cond) { body }; result
        case LabelDef(lname, Nil,
            Block(List(
                If(cond,
                    Block(bodyStats, Apply(target @ Ident(lname2), Nil)),
                    Literal(_))),
                result)) if (target.symbol == sym) =>
          js.Block(
              js.While(genExpr(cond), js.Block(bodyStats map genStat)),
              genExpr(result))

        // while (true) { body }
        case LabelDef(lname, Nil,
            Block(bodyStats,
                Apply(target @ Ident(lname2), Nil))) if (target.symbol == sym) =>
          js.While(js.BooleanLiteral(true), js.Block(bodyStats map genStat))

        // while (false) { body }
        case LabelDef(lname, Nil, Literal(Constant(()))) =>
          js.Skip()

        // do { body } while (cond)
        case LabelDef(lname, Nil,
            Block(bodyStats,
                If(cond,
                    Apply(target @ Ident(lname2), Nil),
                    Literal(_)))) if (target.symbol == sym) =>
          js.DoWhile(js.Block(bodyStats map genStat), genExpr(cond))

        // do { body } while (cond); result
        case LabelDef(lname, Nil,
            Block(
                bodyStats :+
                If(cond,
                    Apply(target @ Ident(lname2), Nil),
                    Literal(_)),
                result)) if (target.symbol == sym) =>
          js.Block(
              js.DoWhile(js.Block(bodyStats map genStat), genExpr(cond)),
              genExpr(result))

        case _ =>
          abort("Found unknown label def at "+tree.pos+": "+tree)
      }
    }

    /** Gen JS code for a try..catch or try..finally block
     *
     *  try..finally blocks are compiled straightforwardly to try..finally
     *  blocks of JS.
     *
     *  try..catch blocks are a bit more subtle, as JS does not have
     *  type-based selection of exceptions to catch. We thus encode explicitly
     *  the type tests, like in:
     *
     *  try { ... }
     *  catch (e) {
     *    if (e.isInstanceOf[IOException]) { ... }
     *    else if (e.isInstanceOf[Exception]) { ... }
     *    else {
     *      throw e; // default, re-throw
     *    }
     *  }
     */
    def genTry(tree: Try, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos
      val Try(block, catches, finalizer) = tree

      val blockAST = genStatOrExpr(block, isStat)
      val exceptIdent = freshLocalIdent("ex")
      val exceptVar = js.VarRef(exceptIdent, mutable = true)(jstpe.AnyType)
      val resultType = toIRType(tree.tpe)

      val handlerAST = {
        if (catches.isEmpty) {
          js.EmptyTree
        } else {
          val mightCatchJavaScriptException = catches.exists { caseDef =>
            caseDef.pat match {
              case Typed(Ident(nme.WILDCARD), tpt) =>
                isMaybeJavaScriptException(tpt.tpe)
              case Ident(nme.WILDCARD) =>
                true
              case pat @ Bind(_, _) =>
                isMaybeJavaScriptException(pat.symbol.tpe)
            }
          }

          val elseHandler: js.Tree =
            if (mightCatchJavaScriptException)
              js.Throw(js.CallHelper("unwrapJavaScriptException", exceptVar)(jstpe.AnyType))
            else
              js.Throw(exceptVar)

          val handler0 = catches.foldRight(elseHandler) { (caseDef, elsep) =>
            implicit val pos = caseDef.pos
            val CaseDef(pat, _, body) = caseDef

            // Extract exception type and variable
            val (tpe, boundVar) = (pat match {
              case Typed(Ident(nme.WILDCARD), tpt) =>
                (tpt.tpe, None)
              case Ident(nme.WILDCARD) =>
                (ThrowableClass.tpe, None)
              case Bind(_, _) =>
                (pat.symbol.tpe, Some(encodeLocalSym(pat.symbol)))
            })

            // Generate the body that must be executed if the exception matches
            val bodyWithBoundVar = (boundVar match {
              case None =>
                genStatOrExpr(body, isStat)
              case Some(bv) =>
                val bvTpe = toIRType(tpe)
                js.Block(
                    js.VarDef(bv, bvTpe, mutable = false, js.Cast(exceptVar, bvTpe)),
                    genStatOrExpr(body, isStat))
            })

            // Generate the test
            if (tpe == ThrowableClass.tpe) {
              bodyWithBoundVar
            } else {
              val cond = genIsInstanceOf(exceptVar, tpe)
              js.If(cond, bodyWithBoundVar, elsep)(resultType)
            }
          }

          if (mightCatchJavaScriptException) {
            js.Block(
                js.Assign(exceptVar,
                    js.CallHelper("wrapJavaScriptException", exceptVar)(
                        encodeClassType(ThrowableClass))),
                handler0)
          } else {
            handler0
          }
        }
      }

      val finalizerAST = genStat(finalizer) match {
        case js.Skip() => js.EmptyTree
        case ast       => ast
      }

      if (handlerAST == js.EmptyTree && finalizerAST == js.EmptyTree) blockAST
      else js.Try(blockAST, exceptIdent, handlerAST, finalizerAST)(resultType)
    }

    /** Gen JS code for an Apply node (method call)
     *
     *  There's a whole bunch of varieties of Apply nodes: regular method
     *  calls, super calls, constructor calls, isInstanceOf/asInstanceOf,
     *  primitives, JS calls, etc. They are further dispatched in here.
     */
    def genApply(tree: Apply, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun, args) = tree

      fun match {
        case TypeApply(_, _) =>
          genApplyTypeApply(tree)

        case Select(Super(_, _), _) =>
          genSuperCall(tree)

        case Select(New(_), nme.CONSTRUCTOR) =>
          genApplyNew(tree)

        case _ =>
          val sym = fun.symbol

          if (sym.isLabel) {
            genLabelApply(tree)
          } else if (scalaPrimitives.isPrimitive(sym)) {
            genPrimitiveOp(tree, isStat)
          } else if (currentRun.runDefinitions.isBox(sym)) {
            // Box a primitive value (cannot be Unit)
            val arg = args.head
            makePrimitiveBox(genExpr(arg), arg.tpe)
          } else if (currentRun.runDefinitions.isUnbox(sym)) {
            // Unbox a primitive value (cannot be Unit)
            val arg = args.head
            makePrimitiveUnbox(genExpr(arg), tree.tpe)
          } else {
            genNormalApply(tree, isStat)
          }
      }
    }

    /** Gen an Apply with a TypeApply method.
     *  Only isInstanceOf and asInstanceOf keep their type argument until the
     *  backend.
     */
    private def genApplyTypeApply(tree: Apply): js.Tree = {
      implicit val pos = tree.pos
      val Apply(TypeApply(fun @ Select(obj, _), targs), _) = tree
      val sym = fun.symbol

      val cast = sym match {
        case Object_isInstanceOf => false
        case Object_asInstanceOf => true
        case _ =>
          abort("Unexpected type application " + fun +
              "[sym: " + sym.fullName + "]" + " in: " + tree)
      }

      val to = targs.head.tpe
      val l = toTypeKind(obj.tpe)
      val r = toTypeKind(to)
      val source = genExpr(obj)

      if (l.isValueType && r.isValueType) {
        if (cast)
          genConversion(l, r, source)
        else
          js.BooleanLiteral(l == r)
      } else if (l.isValueType) {
        val result = if (cast) {
          val ctor = ClassCastExceptionClass.info.member(
              nme.CONSTRUCTOR).suchThat(_.tpe.params.isEmpty)
          js.Throw(genNew(ClassCastExceptionClass, ctor, Nil))
        } else {
          js.BooleanLiteral(false)
        }
        js.Block(source, result) // eval and discard source
      } else if (r.isValueType) {
        assert(!cast, s"Unexpected asInstanceOf from ref type to value type")
        genIsInstanceOf(source, boxedClass(to.typeSymbol).tpe)
      } else {
        if (cast)
          genAsInstanceOf(source, to)
        else
          genIsInstanceOf(source, to)
      }
    }

    /** Gen JS code for a super call, of the form Class.super[mix].fun(args).
     *
     *  This does not include calls defined in mixin traits, as these are
     *  already desugared by the 'mixin' phase. Only calls to super classes
     *  remain.
     *  Since a class has exactly one direct superclass, and calling a method
     *  two classes above the current one is invalid, the `mix` item is
     *  irrelevant.
     */
    private def genSuperCall(tree: Apply): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun @ Select(sup @ Super(_, mix), _), args) = tree
      val sym = fun.symbol

      if (sym == Object_getClass) {
        // The only helper that must also be used when doing a super call
        js.CallHelper(MethodWithHelperInEnv(sym), genThis())(toIRType(tree.tpe))
      } else {
        val superCall = genStaticApplyMethod(
            genThis()(sup.pos), sym, args map genExpr)

        // Initialize the module instance just after the super constructor call.
        if (isStaticModule(currentClassSym) && !isModuleInitialized &&
            currentMethodSym.isClassConstructor) {
          isModuleInitialized = true
          val thisType = jstpe.ClassType(encodeClassFullName(currentClassSym))
          val initModule = js.StoreModule(thisType, js.This()(thisType))
          js.Block(superCall, initModule, js.This()(thisType))
        } else {
          superCall
        }
      }
    }

    /** Gen JS code for a constructor call (new).
     *  Further refined into:
     *  * new String(...)
     *  * new of a hijacked boxed class
     *  * new of an anonymous function class that was recorded as JS function
     *  * new of a raw JS class
     *  * new Array
     *  * regular new
     */
    private def genApplyNew(tree: Apply): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun @ Select(New(tpt), nme.CONSTRUCTOR), args) = tree
      val ctor = fun.symbol
      val tpe = tpt.tpe

      assert(ctor.isClassConstructor,
          "'new' call to non-constructor: " + ctor.name)

      if (isStringType(tpe)) {
        genNewString(tree)
      } else if (isHijackedBoxedClass(tpe.typeSymbol)) {
        genNewHijackedBoxedClass(tpe.typeSymbol, ctor, args map genExpr)
      } else if (translatedAnonFunctions contains tpe.typeSymbol) {
        val (functionMaker, funInfo) = translatedAnonFunctions(tpe.typeSymbol)
        currentMethodInfoBuilder.createsAnonFunction(funInfo)
        functionMaker(args map genExpr)
      } else if (isRawJSType(tpe)) {
        genPrimitiveJSNew(tree)
      } else {
        toTypeKind(tpe) match {
          case arr @ ARRAY(elem) =>
            genNewArray(arr.toIRType, args map genExpr)
          case rt @ REFERENCE(cls) =>
            genNew(cls, ctor, args map genExpr)
          case generatedType =>
            abort(s"Non reference type cannot be instantiated: $generatedType")
        }
      }
    }

    /** Gen jump to a label.
     *  Most label-applys are catched upstream (while and do..while loops,
     *  jumps to next case of a pattern match), but some are still handled here:
     *  * Recursive tail call
     *  * Jump to the end of a pattern match
     */
    private def genLabelApply(tree: Apply): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun, args) = tree
      val sym = fun.symbol

      if (sym == methodTailJumpLabelSym.get) {
        genTailRecLabelApply(tree)
      } else if (sym.name.toString() startsWith "matchEnd") {
        /* Jump the to the end-label of a pattern match
         * Such labels have exactly one argument, which is the result of
         * the pattern match (of type BoxedUnit if the match is in statement
         * position). We simply `return` the argument as the result of the
         * labeled block surrounding the match.
         */
        js.Return(genExpr(args.head), Some(encodeLabelSym(sym)))
      } else {
        /* No other label apply should ever happen. If it does, then we
         * have missed a pattern of LabelDef/LabelApply and some new
         * translation must be found for it.
         */
        abort("Found unknown label apply at "+tree.pos+": "+tree)
      }
    }

    /** Gen a tail-recursive call.
     *
     *  Basically this is compiled into
     *  continue tailCallLoop;
     *  but arguments need to be updated beforehand.
     *
     *  Since the rhs for the new value of an argument can depend on the value
     *  of another argument (and since deciding if it is indeed the case is
     *  impossible in general), new values are computed in temporary variables
     *  first, then copied to the actual variables representing the argument.
     *
     *  Trivial assignments (arg1 = arg1) are eliminated.
     *
     *  If, after elimination of trivial assignments, only one assignment
     *  remains, then we do not use a temporary variable for this one.
     */
    private def genTailRecLabelApply(tree: Apply): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun, args) = tree
      val sym = fun.symbol

      // Prepare quadruplets of (formalArg, irType, tempVar, actualArg)
      // Do not include trivial assignments (when actualArg == formalArg)
      val formalArgs = methodTailJumpFormalArgs.get
      val actualArgs = args map genExpr
      val quadruplets = {
        for {
          (formalArgSym, actualArg) <- formalArgs zip actualArgs
          formalArg = encodeLocalSym(formalArgSym)
          if (actualArg match {
            case js.VarRef(`formalArg`, _) => false
            case _                         => true
          })
        } yield {
          mutatedLocalVars += formalArgSym
          (formalArg, toIRType(formalArgSym.tpe),
              freshLocalIdent("temp$" + formalArg.name),
              actualArg)
        }
      }

      // The actual jump (continue tailCallLoop;)
      val tailJump = js.Continue(Some(js.Ident("tailCallLoop")))

      quadruplets match {
        case Nil => tailJump

        case (formalArg, argType, _, actualArg) :: Nil =>
          js.Block(js.Assign(
              js.VarRef(formalArg, mutable = true)(argType), actualArg),
              tailJump)

        case _ =>
          val tempAssignments =
            for ((_, argType, tempArg, actualArg) <- quadruplets)
              yield js.VarDef(tempArg, argType, mutable = false, actualArg)
          val trueAssignments =
            for ((formalArg, argType, tempArg, _) <- quadruplets)
              yield js.Assign(
                  js.VarRef(formalArg, mutable = true)(argType),
                  js.VarRef(tempArg, mutable = false)(argType))
          js.Block(tempAssignments ++ trueAssignments :+ tailJump)
      }
    }

    /** Gen a "normal" apply (to a true method).
     *
     *  But even these are further refined into:
     *  * Methods implemented by a helper in the environment (typically
     *    because they are defined in an ancestor of a hijacked class, which
     *    means that a value of that type can be a JS value at runtime).
     *  * Methods of java.lang.String, which are redirected to the
     *    RuntimeString trait implementation.
     *  * Calls to methods of raw JS types (Scala.js -> JS bridge)
     *  * Calls to methods in impl classes of traits.
     *  * Regular method call
     */
    private def genNormalApply(tree: Apply, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun @ Select(receiver, _), args) = tree
      val sym = fun.symbol

      def patchedLinkedClassOfClass(sym: Symbol): Symbol = {
        /* Work around a bug of scalac with linkedClassOfClass where package
         * objects are involved (the companion class would somehow exist twice
         * in the scope, making an assertion fail in Symbol.suchThat).
         * Basically this inlines linkedClassOfClass up to companionClass,
         * then replaces the `suchThat` by a `filter` and `head`.
         */
        val flatOwnerInfo = {
          // inline Symbol.flatOwnerInfo because it is protected
          if (sym.needsFlatClasses)
            sym.info
          sym.owner.rawInfo
        }
        val result = flatOwnerInfo.decl(sym.name).filter(_ isCoDefinedWith sym)
        if (!result.isOverloaded) result
        else result.alternatives.head
      }

      def isRawJSCtorDefaultParam = {
        sym.hasFlag(reflect.internal.Flags.DEFAULTPARAM) &&
        sym.owner.isModuleClass &&
        isRawJSType(patchedLinkedClassOfClass(sym.owner).tpe) &&
        nme.defaultGetterToMethod(sym.name) == nme.CONSTRUCTOR
      }

      if (MethodWithHelperInEnv contains sym) {
        if (!isRawJSType(receiver.tpe) && (sym != Object_getClass)) {
          currentMethodInfoBuilder.callsMethod(receiver.tpe.typeSymbol,
              encodeMethodSym(sym))
        }
        val helper = MethodWithHelperInEnv(sym)
        val arguments = (receiver :: args) map genExpr
        js.CallHelper(helper, arguments: _*)(toIRType(tree.tpe))
      } else if (ToStringMaybeOnHijackedClass contains sym) {
        js.Cast(js.JSDotMethodApply(
            js.Cast(genExpr(receiver), jstpe.DynType),
            js.Ident("toString"), Nil), toIRType(tree.tpe))
      } else if (isStringType(receiver.tpe)) {
        genStringCall(tree)
      } else if (isRawJSType(receiver.tpe)) {
        genPrimitiveJSCall(tree, isStat)
      } else if (foreignIsImplClass(sym.owner)) {
        genTraitImplApply(sym, args map genExpr)
      } else if (isRawJSCtorDefaultParam) {
        js.UndefinedParam()(toIRType(sym.tpe.resultType))
      } else if (sym.isClassConstructor) {
        /* See #66: we have to emit a static call to avoid calling a
         * constructor with the same signature in a subclass */
        genStaticApplyMethod(genExpr(receiver), sym, args map genExpr)
      } else {
        genApplyMethod(genExpr(receiver), receiver.tpe, sym, args map genExpr)
      }
    }

    def genStaticApplyMethod(receiver: js.Tree, method: Symbol,
        arguments: List[js.Tree])(implicit pos: Position): js.Tree = {
      val classIdent = encodeClassFullNameIdent(method.owner)
      val methodIdent = encodeMethodSym(method)
      currentMethodInfoBuilder.callsMethodStatic(classIdent, methodIdent)
      js.StaticApply(receiver, jstpe.ClassType(classIdent.name), methodIdent,
          arguments)(toIRType(method.tpe.resultType))
    }

    def genTraitImplApply(method: Symbol, arguments: List[js.Tree])(
        implicit pos: Position): js.Tree = {
      val implIdent = encodeClassFullNameIdent(method.owner)
      val methodIdent = encodeMethodSym(method)
      genTraitImplApply(implIdent, methodIdent, arguments,
          toIRType(method.tpe.resultType))
    }

    def genTraitImplApply(implIdent: js.Ident, methodIdent: js.Ident,
        arguments: List[js.Tree], resultType: jstpe.Type)(
        implicit pos: Position): js.Tree = {
      currentMethodInfoBuilder.callsMethod(implIdent, methodIdent)
      js.TraitImplApply(jstpe.ClassType(implIdent.name), methodIdent,
          arguments)(resultType)
    }

    private lazy val ToStringMaybeOnHijackedClass: Set[Symbol] =
      (Set(CharSequenceClass, StringClass, NumberClass) ++ HijackedBoxedClasses)
        .map(cls => getMemberMethod(cls, nme.toString_))

    private lazy val MethodWithHelperInEnv: Map[Symbol, String] = {
      val m = mutable.Map[Symbol, String](
        Object_toString  -> "objectToString",
        Object_getClass  -> "objectGetClass",
        Object_clone     -> "objectClone",
        Object_finalize  -> "objectFinalize",
        Object_notify    -> "objectNotify",
        Object_notifyAll -> "objectNotifyAll",
        Object_equals    -> "objectEquals",
        Object_hashCode  -> "objectHashCode",
        Array_clone      -> "objectClone"
      )

      def addN(clazz: Symbol, meth: TermName, helperName: String): Unit = {
        for (sym <- getMemberMethod(clazz, meth).alternatives)
          m += sym -> helperName
      }
      def addS(clazz: Symbol, meth: String, helperName: String): Unit =
        addN(clazz, newTermName(meth), helperName)

      addS(CharSequenceClass, "length", "charSequenceLength")
      addS(CharSequenceClass, "charAt", "charSequenceCharAt")
      addS(CharSequenceClass, "subSequence", "charSequenceSubSequence")

      addS(ComparableClass, "compareTo", "comparableCompareTo")

      for (clazz <- StringClass +: HijackedBoxedClasses) {
        addN(clazz, nme.equals_, "objectEquals")
        addN(clazz, nme.hashCode_, "objectHashCode")
        if (clazz != BoxedUnitClass)
          addS(clazz, "compareTo", "comparableCompareTo")
      }

      addS(BoxedBooleanClass, "booleanValue", "booleanBooleanValue")

      for (clazz <- NumberClass +: HijackedNumberClasses) {
        for (pref <- Seq("byte", "short", "int", "long", "float", "double")) {
          val meth = pref+"Value"
          addS(clazz, meth, "number"+meth.capitalize)
          // example: "intValue" -> "numberIntValue"
        }
      }

      addS(BoxedFloatClass, "isNaN", "isNaN")
      addS(BoxedDoubleClass, "isNaN", "isNaN")

      addS(BoxedFloatClass, "isInfinite", "isInfinite")
      addS(BoxedDoubleClass, "isInfinite", "isInfinite")

      m.toMap
    }

    private lazy val CharSequenceClass = requiredClass[java.lang.CharSequence]

    /** Gen JS code for a conversion between primitive value types */
    def genConversion(from: TypeKind, to: TypeKind, value: js.Tree)(
        implicit pos: Position): js.Tree = {
      def int0 = js.IntLiteral(0)
      def int1 = js.IntLiteral(1)
      def float0 = js.DoubleLiteral(0.0)
      def float1 = js.DoubleLiteral(1.0)

      (from, to) match {
        case (LONG,     BOOL) =>
          genLongCall(value, jsnme.notEquals, genLongImplModuleCall(jsnme.Zero))
        case (INT(_),    BOOL) => js.BinaryOp(js.BinaryOp.!==, value, int0)
        case (DOUBLE(_), BOOL) => js.BinaryOp(js.BinaryOp.!==, value, float0)

        case (BOOL, LONG) =>
          js.If(value,
              genLongImplModuleCall(jsnme.One),
              genLongImplModuleCall(jsnme.Zero))(
              jstpe.ClassType(ir.Definitions.RuntimeLongClass))
        case (BOOL, INT(_))    => js.If(value, int1,   int0  )(jstpe.IntType)
        case (BOOL, DOUBLE(_)) => js.If(value, float1, float0)(jstpe.DoubleType)

        case _ => value
      }
    }

    /** Gen JS code for an isInstanceOf test (for reference types only) */
    def genIsInstanceOf(value: js.Tree, to: Type)(
        implicit pos: Position): js.Tree = {

      def genTypeOfTest(typeString: String) = {
        js.BinaryOp(js.BinaryOp.===,
            js.UnaryOp(js.UnaryOp.typeof, value),
            js.StringLiteral(typeString))
      }

      if (isRawJSType(to)) {
        to.typeSymbol match {
          case JSNumberClass    => genTypeOfTest("number")
          case JSStringClass    => genTypeOfTest("string")
          case JSBooleanClass   => genTypeOfTest("boolean")
          case JSUndefinedClass => genTypeOfTest("undefined")
          case sym if sym.isTrait =>
            currentUnit.error(pos,
                s"isInstanceOf[${sym.fullName}] not supported because it is a raw JS trait")
            js.BooleanLiteral(true)
          case sym =>
            js.BinaryOp(js.BinaryOp.instanceof, value, genGlobalJSObject(sym))
        }
      } else {
        val refType = toReferenceType(to)
        currentMethodInfoBuilder.accessesClassData(refType)
        js.IsInstanceOf(value, refType)
      }
    }

    /** Gen JS code for an asInstanceOf cast (for reference types only) */
    def genAsInstanceOf(value: js.Tree, to: Type)(
        implicit pos: Position): js.Tree = {

      def default: js.Tree = {
        val refType = toReferenceType(to)
        currentMethodInfoBuilder.accessesClassData(refType)
        js.AsInstanceOf(value, refType)
      }

      if (isRawJSType(to)) {
        // asInstanceOf on JavaScript is completely erased
        if (value.tpe == jstpe.DynType) value
        else js.Cast(value, jstpe.DynType)
      } else if (FunctionClass.seq contains to.typeSymbol) {
        /* Don't hide a JSFunctionToScala inside a useless cast, otherwise
         * the optimization avoiding double-wrapping in genApply() will not
         * be able to kick in.
         */
        value match {
          case JSFunctionToScala(fun, _) => value
          case _                         => default
        }
      } else {
        default
      }
    }

    /** Gen JS code for a call to a Scala method.
     *  This also registers that the given method is called by the current
     *  method in the method info builder.
     */
    def genApplyMethod(receiver: js.Tree, receiverType: Type,
        methodSym: Symbol, arguments: List[js.Tree])(
        implicit pos: Position): js.Tree = {
      genApplyMethod(receiver, receiverType.typeSymbol, methodSym, arguments)
    }

    /** Gen JS code for a call to a Scala method.
     *  This also registers that the given method is called by the current
     *  method in the method info builder.
     */
    def genApplyMethod(receiver: js.Tree, receiverTypeSym: Symbol,
        methodSym: Symbol, arguments: List[js.Tree])(
        implicit pos: Position): js.Tree = {
      genApplyMethod(receiver, receiverTypeSym,
          encodeMethodSym(methodSym), arguments,
          toIRType(methodSym.tpe.resultType))
    }

    /** Gen JS code for a call to a Scala method.
     *  This also registers that the given method is called by the current
     *  method in the method info builder.
     */
    def genApplyMethod(receiver: js.Tree, receiverType: Type,
        methodIdent: js.Ident, arguments: List[js.Tree], resultType: jstpe.Type)(
        implicit pos: Position): js.Tree = {
      genApplyMethod(receiver, receiverType.typeSymbol, methodIdent,
          arguments, resultType)
    }

    /** Gen JS code for a call to a Scala method.
     *  This also registers that the given method is called by the current
     *  method in the method info builder.
     */
    def genApplyMethod(receiver: js.Tree, receiverTypeSym: Symbol,
        methodIdent: js.Ident, arguments: List[js.Tree], resultType: jstpe.Type)(
        implicit pos: Position): js.Tree = {
      currentMethodInfoBuilder.callsMethod(receiverTypeSym, methodIdent)
      js.Apply(receiver, methodIdent, arguments)(resultType)
    }

    /** Gen JS code for a call to a Scala class constructor.
     *
     *  This also registers that the given class is instantiated by the current
     *  method, and that the given constructor is called, in the method info
     *  builder.
     */
    def genNew(clazz: Symbol, ctor: Symbol, arguments: List[js.Tree])(
        implicit pos: Position): js.Tree = {
      if (clazz.isAnonymousFunction)
        instantiatedAnonFunctions += clazz
      assert(!isRawJSFunctionDef(clazz),
          s"Trying to instantiate a raw JS function def $clazz")
      val ctorIdent = encodeMethodSym(ctor)
      currentMethodInfoBuilder.instantiatesClass(clazz)
      currentMethodInfoBuilder.callsMethod(clazz, ctorIdent)
      js.New(jstpe.ClassType(encodeClassFullName(clazz)),
          ctorIdent, arguments)
    }

    /** Gen JS code for a call to a constructor of a hijacked boxed class.
     *  All of these have 2 constructors: one with the primitive
     *  value, which is erased, and one with a String, which is
     *  equivalent to BoxedClass.valueOf(arg).
     */
    private def genNewHijackedBoxedClass(clazz: Symbol, ctor: Symbol,
        arguments: List[js.Tree])(implicit pos: Position): js.Tree = {
      assert(arguments.size == 1)
      if (isStringType(ctor.tpe.params.head.tpe)) {
        // BoxedClass.valueOf(arg)
        val companion = clazz.companionModule.moduleClass
        val valueOf = getMemberMethod(companion, nme.valueOf) suchThat { s =>
          s.tpe.params.size == 1 && isStringType(s.tpe.params.head.tpe)
        }
        genApplyMethod(genLoadModule(companion), companion, valueOf, arguments)
      } else {
        // erased
        arguments.head
      }
    }

    /** Gen JS code for creating a new Array: new Array[T](length)
     *  For multidimensional arrays (dimensions > 1), the arguments can
     *  specify up to `dimensions` lengths for the first dimensions of the
     *  array.
     */
    def genNewArray(arrayType: jstpe.ArrayType, arguments: List[js.Tree])(
        implicit pos: Position): js.Tree = {
      assert(arguments.length <= arrayType.dimensions,
          "too many arguments for array constructor: found " + arguments.length +
          " but array has only " + arrayType.dimensions + " dimension(s)")

      currentMethodInfoBuilder.accessesClassData(arrayType)
      js.NewArray(arrayType, arguments)
    }

    /** Gen JS code for an array literal.
     */
    def genArrayValue(tree: Tree): js.Tree = {
      implicit val pos = tree.pos
      val ArrayValue(tpt @ TypeTree(), elems) = tree

      val arrType = toReferenceType(tree.tpe).asInstanceOf[jstpe.ArrayType]
      currentMethodInfoBuilder.accessesClassData(arrType)
      js.ArrayValue(arrType, elems map genExpr)
    }

    /** Gen JS code for a Match, i.e., a switch-able pattern match
     *  Eventually, this is compiled into a JS switch construct. But because
     *  we can be in expression position, and a JS switch cannot be given a
     *  meaning in expression position, we emit a JS "match" construct (which
     *  does not need the `break`s in each case. `JSDesugaring` will transform
     *  that in a switch.
     *
     *  Some caveat here. It may happen that there is a guard in here, despite
     *  the fact that switches cannot have guards (in the JVM nor in JS).
     *  The JVM backend emits a jump to the default clause when a guard is not
     *  fulfilled. We cannot do that. Instead, currently we duplicate the body
     *  of the default case in the else branch of the guard test.
     */
    def genMatch(tree: Tree, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos
      val Match(selector, cases) = tree

      val expr = genExpr(selector)
      val resultType = toIRType(tree.tpe)

      val List(defaultBody0) = for {
        CaseDef(Ident(nme.WILDCARD), EmptyTree, body) <- cases
      } yield body

      val (defaultBody, defaultLabelSym) = defaultBody0 match {
        case LabelDef(_, Nil, rhs) if hasSynthCaseSymbol(defaultBody0) =>
          (rhs, defaultBody0.symbol)
        case _ =>
          (defaultBody0, NoSymbol)
      }

      val genDefaultBody = genStatOrExpr(defaultBody, isStat)

      var clauses: List[(List[js.Tree], js.Tree)] = Nil
      var elseClause: js.Tree = js.EmptyTree

      for (caze @ CaseDef(pat, guard, body) <- cases) {
        assert(guard == EmptyTree)

        def genBody() = body match {
          // Yes, this will duplicate the default body in the output
          case If(cond, thenp, app @ Apply(_, Nil))
              if app.symbol == defaultLabelSym =>
            js.If(genExpr(cond), genStatOrExpr(thenp, isStat), genDefaultBody)(
                resultType)(body.pos)
          case If(cond, thenp, Block(List(app @ Apply(_, Nil)), _))
              if app.symbol == defaultLabelSym =>
            js.If(genExpr(cond), genStatOrExpr(thenp, isStat), genDefaultBody)(
                resultType)(body.pos)

          case _ =>
            genStatOrExpr(body, isStat)
        }

        pat match {
          case lit: Literal =>
            clauses = (List(genExpr(lit)), genBody()) :: clauses
          case Ident(nme.WILDCARD) =>
            elseClause = genDefaultBody
          case Alternative(alts) =>
            val genAlts = {
              alts map {
                case lit: Literal => genExpr(lit)
                case _ =>
                  abort("Invalid case in alternative in switch-like pattern match: " +
                      tree + " at: " + tree.pos)
              }
            }
            clauses = (genAlts, genBody()) :: clauses
          case _ =>
            abort("Invalid case statement in switch-like pattern match: " +
                tree + " at: " + (tree.pos))
        }
      }

      js.Match(expr, clauses.reverse, elseClause)(resultType)
    }

    private def genBlock(tree: Block, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos
      val Block(stats, expr) = tree

      /** Predicate satisfied by LabelDefs produced by the pattern matcher */
      def isCaseLabelDef(tree: Tree) =
        tree.isInstanceOf[LabelDef] && hasSynthCaseSymbol(tree)

      def translateMatch(expr: LabelDef) = {
        /* Block that appeared as the result of a translated match
         * Such blocks are recognized by having at least one element that is
         * a so-called case-label-def.
         * The method `genTranslatedMatch()` takes care of compiling the
         * actual match.
         *
         * The assumption is once we encounter a case, the remainder of the
         * block will consist of cases.
         * The prologue may be empty, usually it is the valdef that stores
         * the scrut.
         */
        val (prologue, cases) = stats.span(s => !isCaseLabelDef(s))
        assert(cases.forall(isCaseLabelDef),
            "Assumption on the form of translated matches broken: " + tree)

        val genPrologue = prologue map genStat
        val translatedMatch =
          genTranslatedMatch(cases.map(_.asInstanceOf[LabelDef]), expr)

        js.Block(genPrologue :+ translatedMatch)
      }

      expr match {
        case expr: LabelDef if isCaseLabelDef(expr) =>
          translateMatch(expr)

        // Sometimes the pattern matcher casts its final result
        case Apply(TypeApply(Select(expr: LabelDef, nme.asInstanceOf_Ob), _), _)
            if isCaseLabelDef(expr) =>
          translateMatch(expr)

        case _ =>
          assert(!stats.exists(isCaseLabelDef), "Found stats with case label " +
              s"def in non-match block at ${tree.pos}: $tree")

          /* Normal block */
          val statements = stats map genStat
          val expression = genStatOrExpr(expr, isStat)
          js.Block(statements :+ expression)
      }
    }

    /** Gen JS code for a translated match
     *
     *  This implementation relies heavily on the patterns of trees emitted
     *  by the current pattern match phase (as of Scala 2.10).
     *
     *  The trees output by the pattern matcher are assumed to follow these
     *  rules:
     *  * Each case LabelDef (in `cases`) must not take any argument.
     *  * The last one must be a catch-all (case _ =>) that never falls through.
     *  * Jumps to the `matchEnd` are allowed anywhere in the body of the
     *    corresponding case label-defs, but not outside.
     *  * Jumps to case label-defs are restricted to jumping to the very next
     *    case, and only in positions denoted by <jump> in:
     *    <case-body> ::=
     *        If(_, <case-body>, <case-body>)
     *      | Block(_, <case-body>)
     *      | <jump>
     *      | _
     *    These restrictions, together with the fact that we are in statement
     *    position (thanks to the above transformation), mean that they can be
     *    simply replaced by `skip`.
     *
     *  To implement jumps to `matchEnd`, which have one argument which is the
     *  result of the match, we enclose all the cases in one big labeled block.
     *  Jumps are then compiled as `return`s out of the block.
     */
    def genTranslatedMatch(cases: List[LabelDef],
        matchEnd: LabelDef)(implicit pos: Position): js.Tree = {

      val nextCaseSyms = (cases.tail map (_.symbol)) :+ NoSymbol

      val translatedCases = for {
        (LabelDef(_, Nil, rhs), nextCaseSym) <- cases zip nextCaseSyms
      } yield {
        def genCaseBody(tree: Tree): js.Tree = {
          implicit val pos = tree.pos
          tree match {
            case If(cond, thenp, elsep) =>
              js.If(genExpr(cond), genCaseBody(thenp), genCaseBody(elsep))(
                  jstpe.NoType)

            case Block(stats, expr) =>
              js.Block((stats map genStat) :+ genCaseBody(expr))

            case Apply(_, Nil) if tree.symbol == nextCaseSym =>
              js.Skip()

            case _ =>
              genStat(tree)
          }
        }

        genCaseBody(rhs)
      }

      js.Labeled(encodeLabelSym(matchEnd.symbol), toIRType(matchEnd.tpe),
          js.Block(translatedCases))
    }

    /** Gen JS code for a primitive method call */
    private def genPrimitiveOp(tree: Apply, isStat: Boolean): js.Tree = {
      import scalaPrimitives._

      implicit val pos = tree.pos

      val sym = tree.symbol
      val Apply(fun @ Select(receiver, _), args) = tree

      val code = scalaPrimitives.getPrimitive(sym, receiver.tpe)

      if (isArithmeticOp(code) || isLogicalOp(code) || isComparisonOp(code))
        genSimpleOp(tree, receiver :: args, code)
      else if (code == scalaPrimitives.CONCAT)
        genStringConcat(tree, receiver, args)
      else if (code == HASH)
        genScalaHash(tree, receiver)
      else if (isArrayOp(code))
        genArrayOp(tree, code)
      else if (code == SYNCHRONIZED)
        genSynchronized(tree, isStat)
      else if (isCoercion(code))
        genCoercion(tree, receiver, code)
      else if (jsPrimitives.isJavaScriptPrimitive(code))
        genJSPrimitive(tree, receiver, args, code)
      else
        abort("Unknown primitive operation: " + sym.fullName + "(" +
            fun.symbol.simpleName + ") " + " at: " + (tree.pos))
    }

    /** Gen JS code for a simple operation (arithmetic, logical, or comparison) */
    private def genSimpleOp(tree: Apply, args: List[Tree], code: Int): js.Tree = {
      import scalaPrimitives._

      implicit val pos = tree.pos

      def needLongConv(ltpe: Type, rtpe: Type) =
        (isLongType(ltpe) || isLongType(rtpe)) &&
        !(toTypeKind(ltpe).isInstanceOf[DOUBLE] ||
          toTypeKind(rtpe).isInstanceOf[DOUBLE] ||
          isStringType(ltpe) || isStringType(rtpe))

      val sources = args map genExpr

      def resultType = toIRType(tree.tpe)

      sources match {
        // Unary op on long
        case List(source) if isLongType(args.head.tpe) => code match {
            case POS => genLongCall(source, nme.UNARY_+)
            case NEG => genLongCall(source, nme.UNARY_-)
            case NOT => genLongCall(source, nme.UNARY_~)
            case _   => abort("Unknown or invalid op code on Long: " + code)
          }

        // Unary operation
        case List(source) =>
          (code match {
            case POS =>
              js.UnaryOp((resultType: @unchecked) match {
                case jstpe.IntType    => js.UnaryOp.Int_+
                case jstpe.DoubleType => js.UnaryOp.Double_+
              }, source)
            case NEG =>
              js.UnaryOp((resultType: @unchecked) match {
                case jstpe.IntType    => js.UnaryOp.Int_-
                case jstpe.DoubleType => js.UnaryOp.Double_-
              }, source)
            case NOT =>
              js.UnaryOp(js.UnaryOp.Int_~, source)
            case ZNOT =>
              js.UnaryOp(js.UnaryOp.Boolean_!, source)
            case _ =>
              abort("Unknown unary operation code: " + code)
          })

        // Binary operation requiring conversion to Long of both sides
        case List(lsrc, rsrc) if needLongConv(args(0).tpe, args(1).tpe) =>
          def toLong(tree: js.Tree, tpe: Type) = tpe.typeSymbol match {
              case ByteClass  => genLongModuleCall(jsnme.fromByte,  tree)
              case ShortClass => genLongModuleCall(jsnme.fromShort, tree)
              case CharClass  => genLongModuleCall(jsnme.fromChar,  tree)
              case IntClass   => genLongModuleCall(jsnme.fromInt,   tree)
              case LongClass  => tree
            }

          val ltree = toLong(lsrc, args(0).tpe)
          val rtree = toLong(rsrc, args(1).tpe)
          val rtLongTpe = RuntimeLongClass.tpe

          def genShift(methodName: TermName): js.Tree = {
            val rtree =
              if (isLongType(args(1).tpe)) genLongCall(rsrc, jsnme.toInt)
              else rsrc
            genOlLongCall(ltree, methodName, rtree)(IntTpe)
          }

          code match {
            case ADD => genOlLongCall(ltree, nme.PLUS,  rtree)(rtLongTpe)
            case SUB => genOlLongCall(ltree, nme.MINUS, rtree)(rtLongTpe)
            case MUL => genOlLongCall(ltree, nme.MUL,   rtree)(rtLongTpe)
            case DIV => genOlLongCall(ltree, nme.DIV,   rtree)(rtLongTpe)
            case MOD => genOlLongCall(ltree, nme.MOD,   rtree)(rtLongTpe)
            case OR  => genOlLongCall(ltree, nme.OR,    rtree)(rtLongTpe)
            case XOR => genOlLongCall(ltree, nme.XOR,   rtree)(rtLongTpe)
            case AND => genOlLongCall(ltree, nme.AND,   rtree)(rtLongTpe)
            case LT  => genOlLongCall(ltree, nme.LT,    rtree)(rtLongTpe)
            case LE  => genOlLongCall(ltree, nme.LE,    rtree)(rtLongTpe)
            case GT  => genOlLongCall(ltree, nme.GT,    rtree)(rtLongTpe)
            case GE  => genOlLongCall(ltree, nme.GE,    rtree)(rtLongTpe)
            case EQ  => genOlLongCall(ltree, nme.equals_, rtree)(rtLongTpe)
            case NE  => genOlLongCall(ltree, jsnme.notEquals, rtree)(rtLongTpe)
            case LSL => genShift(nme.LSL)
            case LSR => genShift(nme.LSR)
            case ASR => genShift(nme.ASR)
            case _ =>
              abort("Unknown binary operation code: " + code)
          }

        // Binary operation
        case List(lsrc_in, rsrc_in) =>
          def fromLong(tree: js.Tree, tpe: Type) = tpe.typeSymbol match {
            // If we end up with a long, target must be float
            case LongClass => genLongCall(tree, jsnme.toDouble)
            case _         => tree
          }

          val lsrc = fromLong(lsrc_in, args(0).tpe)
          val rsrc = fromLong(rsrc_in, args(1).tpe)

          def genEquality(eqeq: Boolean, not: Boolean) = {
            if (eqeq &&
                toTypeKind(args(0).tpe).isReferenceType &&
                !isRawJSType(args(0).tpe) &&
                !isRawJSType(args(1).tpe) &&
                // don't call equals if we have a literal null at rhs
                !rsrc.isInstanceOf[js.Null]
                ) {
              val body = genEqEqPrimitive(args(0), args(1), lsrc, rsrc)
              if (not) js.UnaryOp(js.UnaryOp.Boolean_!, body) else body
            } else
              js.BinaryOp(if (not) js.BinaryOp.!== else js.BinaryOp.===, lsrc, rsrc)
          }

          (code: @switch) match {
            case EQ => genEquality(eqeq = true, not = false)
            case NE => genEquality(eqeq = true, not = true)
            case ID => genEquality(eqeq = false, not = false)
            case NI => genEquality(eqeq = false, not = true)
            case _ =>
              import js.BinaryOp._
              val op = (resultType: @unchecked) match {
                case jstpe.IntType =>
                  (code: @switch) match {
                    case ADD => Int_+
                    case SUB => Int_-
                    case MUL => Int_*
                    case DIV => Int_/
                    case MOD => Int_%
                    case OR  => Int_|
                    case AND => Int_&
                    case XOR => Int_^
                    case LSL => Int_<<
                    case LSR => Int_>>>
                    case ASR => Int_>>
                  }
                case jstpe.DoubleType =>
                  (code: @switch) match {
                    case ADD => Double_+
                    case SUB => Double_-
                    case MUL => Double_*
                    case DIV => Double_/
                    case MOD => Double_%
                  }
                case jstpe.BooleanType =>
                  (code: @switch) match {
                    case LT   => <
                    case LE   => <=
                    case GT   => >
                    case GE   => >=
                    case OR   => Boolean_|
                    case AND  => Boolean_&
                    case XOR  => Boolean_^
                    case ZOR  => Boolean_||
                    case ZAND => Boolean_&&
                  }
              }
              js.BinaryOp(op, lsrc, rsrc)
          }

        case _ =>
          abort("Too many arguments for primitive function: " + tree)
      }
    }

    /** Gen JS code for a call to Any.== */
    def genEqEqPrimitive(l: Tree, r: Tree, lsrc: js.Tree, rsrc: js.Tree)(
        implicit pos: Position): js.Tree = {
      /** True if the equality comparison is between values that require the use of the rich equality
        * comparator (scala.runtime.Comparator.equals). This is the case when either side of the
        * comparison might have a run-time type subtype of java.lang.Number or java.lang.Character.
        * When it is statically known that both sides are equal and subtypes of Number of Character,
        * not using the rich equality is possible (their own equals method will do ok.)*/
      def mustUseAnyComparator: Boolean = {
        def areSameFinals = l.tpe.isFinalType && r.tpe.isFinalType && (l.tpe =:= r.tpe)
        !areSameFinals && isMaybeBoxed(l.tpe.typeSymbol) && isMaybeBoxed(r.tpe.typeSymbol)
      }

      val function = if (mustUseAnyComparator) "anyEqEq" else "anyRefEqEq"
      js.CallHelper(function, lsrc, rsrc)(jstpe.BooleanType)
    }

    /** Gen JS code for string concatenation.
     */
    private def genStringConcat(tree: Apply, receiver: Tree,
        args: List[Tree]): js.Tree = {
      implicit val pos = tree.pos

      /* Primitive number types such as scala.Int have a
       *   def +(s: String): String
       * method, which is why we have to box the lhs sometimes.
       * Otherwise, both lhs and rhs are already reference types (Any of String)
       * so boxing is not necessary (in particular, rhs is never a primitive).
       */
      assert(!isPrimitiveValueType(receiver.tpe) || isStringType(args.head.tpe))
      assert(!isPrimitiveValueType(args.head.tpe))

      val rhs = genExpr(args.head)

      val lhs = {
        val lhs0 = genExpr(receiver)
        // Box the receiver if it is a primitive value
        if (!isPrimitiveValueType(receiver.tpe)) lhs0
        else makePrimitiveBox(lhs0, receiver.tpe)
      }

      js.BinaryOp(js.BinaryOp.String_+, lhs, rhs)
    }

    /** Gen JS code for a call to Any.## */
    private def genScalaHash(tree: Apply, receiver: Tree): js.Tree = {
      implicit val pos = tree.pos

      val instance = genLoadModule(ScalaRunTimeModule)
      val arguments = List(genExpr(receiver))
      val sym = getMember(ScalaRunTimeModule, nme.hash_)

      genApplyMethod(instance, ScalaRunTimeModule.moduleClass, sym, arguments)
    }

    /** Gen JS code for an array operation (get, set or length) */
    private def genArrayOp(tree: Tree, code: Int): js.Tree = {
      import scalaPrimitives._

      implicit val pos = tree.pos

      val Apply(Select(arrayObj, _), args) = tree
      val arrayValue = genExpr(arrayObj)
      val arguments = args map genExpr

      def genSelect() = {
        val elemIRType =
          toTypeKind(arrayObj.tpe).asInstanceOf[ARRAY].elem.toIRType
        js.ArraySelect(arrayValue, arguments(0))(elemIRType)
      }

      if (scalaPrimitives.isArrayGet(code)) {
        // get an item of the array
        assert(args.length == 1,
            s"Array get requires 1 argument, found ${args.length} in $tree")
        genSelect()
      } else if (scalaPrimitives.isArraySet(code)) {
        // set an item of the array
        assert(args.length == 2,
            s"Array set requires 2 arguments, found ${args.length} in $tree")
        js.Assign(genSelect(), arguments(1))
      } else {
        // length of the array
        js.ArrayLength(arrayValue)
      }
    }

    /** Gen JS code for a call to AnyRef.synchronized */
    private def genSynchronized(tree: Apply, isStat: Boolean): js.Tree = {
      /* JavaScript is single-threaded, so we can drop the
       * synchronization altogether.
       */
      val Apply(Select(receiver, _), List(arg)) = tree
      val newReceiver = genExpr(receiver)
      val newArg = genStatOrExpr(arg, isStat)
      newReceiver match {
        case js.This() =>
          // common case for which there is no side-effect nor NPE
          newArg
        case _ =>
          js.Block(
              js.CallHelper("checkNonNull", newReceiver)(
                  newReceiver.tpe)(newReceiver.pos),
              newArg)(newArg.pos)
      }
    }

    /** Gen JS code for a coercion */
    private def genCoercion(tree: Apply, receiver: Tree, code: Int): js.Tree = {
      import scalaPrimitives._

      implicit val pos = tree.pos

      val source = genExpr(receiver)

      def source2int = (code: @switch) match {
        case F2C | D2C | F2B | D2B | F2S | D2S | F2I | D2I =>
          js.UnaryOp(js.UnaryOp.DoubleToInt , source)
        case _ =>
          source
      }

      (code: @scala.annotation.switch) match {
        // From Long to something
        case L2B =>
          genLongCall(source, jsnme.toByte)
        case L2S =>
          genLongCall(source, jsnme.toShort)
        case L2C =>
          genLongCall(source, jsnme.toChar)
        case L2I =>
          genLongCall(source, jsnme.toInt)
        case L2F =>
          genLongCall(source, jsnme.toFloat)
        case L2D =>
          genLongCall(source, jsnme.toDouble)

        // From something to long
        case B2L =>
          genLongModuleCall(jsnme.fromByte, source)
        case S2L =>
          genLongModuleCall(jsnme.fromShort, source)
        case C2L =>
          genLongModuleCall(jsnme.fromChar, source)
        case I2L =>
          genLongModuleCall(jsnme.fromInt, source)
        case F2L =>
          genLongModuleCall(jsnme.fromFloat, source)
        case D2L =>
          genLongModuleCall(jsnme.fromDouble, source)

        // Conversions to chars (except for Long)
        case B2C | S2C | I2C | F2C | D2C =>
          js.BinaryOp(js.BinaryOp.Int_&, source2int, js.IntLiteral(0xffff))

        // To Byte, need to crop at signed 8-bit
        case C2B | S2B | I2B | F2B | D2B =>
          // note: & 0xff would not work because of negative values
          js.BinaryOp(js.BinaryOp.Int_>>,
              js.BinaryOp(js.BinaryOp.Int_<<, source2int, js.IntLiteral(24)),
              js.IntLiteral(24))

        // To Short, need to crop at signed 16-bit
        case C2S | I2S | F2S | D2S =>
          // note: & 0xffff would not work because of negative values
          js.BinaryOp(js.BinaryOp.Int_>>,
              js.BinaryOp(js.BinaryOp.Int_<<, source2int, js.IntLiteral(16)),
              js.IntLiteral(16))

        // To Int, need to crop at signed 32-bit
        case F2I | D2I =>
          source2int

        case _ => source
      }
    }

    /** Gen JS code for an ApplyDynamic
     *  ApplyDynamic nodes appear as the result of calls to methods of a
     *  structural type.
     *
     *  Most unfortunately, earlier phases of the compiler assume too much
     *  about the backend, namely, they believe arguments and the result must
     *  be boxed, and do the boxing themselves. This decision should be left
     *  to the backend, but it's not, so we have to undo these boxes.
     *  Note that this applies to parameter types only. The return type is boxed
     *  anyway since we do not know it's exact type.
     *
     *  This then generates a call to the reflective call proxy for the given
     *  arguments.
     */
    private def genApplyDynamic(tree: ApplyDynamic): js.Tree = {
      implicit val pos = tree.pos

      val sym = tree.symbol
      val params = sym.tpe.params

      /** check if the method we are invoking is eq or ne. they cannot be
       *  overridden since they are final. If this is true, we only emit a
       *  `===` or `!==`.
       */
      val isEqOrNeq = (sym.name == nme.eq || sym.name == nme.ne) &&
        params.size == 1 && params.head.tpe.typeSymbol == ObjectClass

      /** check if the method we are invoking conforms to a method on
       *  scala.Array. If this is the case, we check that case specially at
       *  runtime to avoid having reflective call proxies on scala.Array.
       *  (Also, note that the element type of Array#update is not erased and
       *  therefore the method name mangling would turn out wrong)
       *
       *  Note that we cannot check if the expected return type is correct,
       *  since this type information is already erased.
       */
      def isArrayLikeOp = {
        sym.name == nme.update &&
          params.size == 2 && params.head.tpe.typeSymbol == IntClass ||
        sym.name == nme.apply &&
          params.size == 1 && params.head.tpe.typeSymbol == IntClass ||
        sym.name == nme.length &&
          params.size == 0 ||
        sym.name == nme.clone_ &&
          params.size == 0
      }

      /**
       * Tests whether one of our reflective "boxes" for primitive types
       * implements the particular method. If this is the case
       * (result != NoSymbol), we generate a runtime instance check if we are
       * dealing with the appropriate primitive type.
       */
      def matchingSymIn(clazz: Symbol) = clazz.tpe.member(sym.name).suchThat { s =>
        val sParams = s.tpe.params
        !s.isBridge &&
        params.size == sParams.size &&
        (params zip sParams).forall { case (s1,s2) =>
          s1.tpe =:= s2.tpe
        }
      }

      val ApplyDynamic(receiver, args) = tree

      if (isEqOrNeq) {
        // Just emit a boxed equality check
        val jsThis = genExpr(receiver)
        val jsThat = genExpr(args.head)
        val op = if (sym.name == nme.eq) js.BinaryOp.=== else js.BinaryOp.!==
        ensureBoxed(js.BinaryOp(op, jsThis, jsThat), BooleanClass.tpe)
      } else {
        // Create a fully-fledged reflective call
        val receiverType = toIRType(receiver.tpe)
        val callTrgIdent = freshLocalIdent()
        val callTrgVarDef =
          js.VarDef(callTrgIdent, receiverType, mutable = false, genExpr(receiver))
        val callTrg = js.VarRef(callTrgIdent, mutable = false)(receiverType)

        val arguments = args zip sym.tpe.params map { case (arg, param) =>
          /* No need for enteringPosterasure, because value classes are not
           * supported as parameters of methods in structural types.
           * We could do it for safety and future-proofing anyway, except that
           * I am weary of calling enteringPosterasure for a reflective method
           * symbol.
           *
           * Note also that this will typically unbox a primitive value that
           * has just been boxed, or will .asInstanceOf[T] an expression which
           * is already of type T. But the optimizer will get rid of that, and
           * reflective calls are not numerous, so we don't complicate the
           * compiler to eliminate them early.
           */
          fromAny(genExpr(arg), param.tpe)
        }

        val proxyIdent = encodeMethodSym(sym, reflProxy = true)
        var callStatement: js.Tree =
          genApplyMethod(callTrg, receiver.tpe, proxyIdent, arguments,
              jstpe.AnyType)

        if (isArrayLikeOp) {
          def genRTCall(method: Symbol, args: js.Tree*) =
            genApplyMethod(genLoadModule(ScalaRunTimeModule),
                ScalaRunTimeModule.moduleClass, method, args.toList)
          val isArrayTree =
            genRTCall(ScalaRunTime_isArray, callTrg, js.IntLiteral(1))
          callStatement = js.If(isArrayTree, {
            sym.name match {
              case nme.update =>
                js.Block(
                    genRTCall(currentRun.runDefinitions.arrayUpdateMethod,
                        callTrg, arguments(0), arguments(1)),
                    js.Undefined()) // Boxed Unit
              case nme.apply =>
                genRTCall(currentRun.runDefinitions.arrayApplyMethod, callTrg,
                    arguments(0))
              case nme.length =>
                genRTCall(currentRun.runDefinitions.arrayLengthMethod, callTrg)
              case nme.clone_ =>
                js.CallHelper("objectClone", callTrg)(jstpe.AnyType)
            }
          }, {
            callStatement
          })(jstpe.AnyType)
        }

        for {
          (primTypeOf, reflBoxClass) <- Seq(
              ("string", RuntimeStringClass),
              ("number", NumberReflectiveCallClass),
              ("boolean", BooleanReflectiveCallClass)
          )
          implMethodSym = matchingSymIn(reflBoxClass)
          if implMethodSym != NoSymbol && implMethodSym.isPublic
        } {
          callStatement = js.If(
              js.BinaryOp(js.BinaryOp.===,
                js.UnaryOp(js.UnaryOp.typeof, callTrg),
                js.StringLiteral(primTypeOf)), {
            val helper = MethodWithHelperInEnv.get(implMethodSym)
            if (helper.isDefined) {
              // This method has a helper, call it
              js.CallHelper(helper.get, callTrg :: arguments:_*)(
                  toIRType(implMethodSym.tpe.resultType))
            } else if (implMethodSym.owner == ObjectClass) {
              /* If we end up here, we have a call to a method in
               * java.lang.Object we cannot support (such as wait).
               * Calls like this only fail reflectively at compile time because
               * some of them exist in the Scala stdlib. DCE will issue a
               * warning in any case.
               */
              currentUnit.error(pos,
                  s"""You tried to call ${implMethodSym.name} on AnyRef reflectively, but this
                     |method does not make sense in Scala.js. You may not call it""".stripMargin)
              js.Undefined()
            } else {
              if (primTypeOf == "string") {
                val (implClass, methodIdent) =
                  encodeImplClassMethodSym(implMethodSym)
                val retTpe = implMethodSym.tpe.resultType
                val castCallTrg = js.Cast(callTrg,
                    toIRType(RuntimeStringClass.toTypeConstructor))
                val rawApply = genTraitImplApply(
                    encodeClassFullNameIdent(implClass),
                    methodIdent,
                    castCallTrg :: arguments,
                    toIRType(retTpe))
                // Box the result of the implementing method if required
                if (isPrimitiveValueType(retTpe))
                  makePrimitiveBox(rawApply, retTpe)
                else
                  rawApply
              } else {
                val (reflBoxClassPatched, callTrg1) = {
                  def isIntOrLongKind(kind: TypeKind) = kind match {
                    case _:INT | LONG => true
                    case _            => false
                  }
                  if (primTypeOf == "number" &&
                      toTypeKind(implMethodSym.tpe.resultType) == DoubleKind &&
                      isIntOrLongKind(toTypeKind(sym.tpe.resultType))) {
                    // This must be an Int, and not a Double
                    (IntegerReflectiveCallClass,
                        js.AsInstanceOf(callTrg,
                            toReferenceType(BoxedIntClass.toTypeConstructor)))
                  } else {
                    (reflBoxClass, callTrg)
                  }
                }
                val castCallTrg =
                  js.Cast(callTrg1, toIRType(
                      reflBoxClassPatched.primaryConstructor.tpe.params.head.tpe))
                val reflBox = genNew(reflBoxClassPatched,
                    reflBoxClassPatched.primaryConstructor, List(castCallTrg))
                genApplyMethod(
                    reflBox,
                    reflBoxClassPatched,
                    proxyIdent,
                    arguments,
                    jstpe.AnyType)
              }
            }
          }, { // else
            callStatement
          })(jstpe.AnyType)
        }

        js.Block(callTrgVarDef, callStatement)
      }
    }

    /** Ensures that the value of the given tree is boxed.
     *  @param expr Tree to be boxed if needed.
     *  @param tpeEnteringPosterasure The type of `expr` as it was entering
     *    the posterasure phase.
     */
    def ensureBoxed(expr: js.Tree, tpeEnteringPosterasure: Type)(
        implicit pos: Position): js.Tree = {

      tpeEnteringPosterasure match {
        case tpe if isPrimitiveValueType(tpe) =>
          makePrimitiveBox(expr, tpe)

        case tpe: ErasedValueType =>
          val boxedClass = tpe.valueClazz
          val ctor = boxedClass.primaryConstructor
          genNew(boxedClass, ctor, List(expr))

        case _ =>
          expr
      }
    }

    /** Extracts a value typed as Any to the given type after posterasure.
     *  @param expr Tree to be extracted.
     *  @param tpeEnteringPosterasure The type of `expr` as it was entering
     *    the posterasure phase.
     */
    def fromAny(expr: js.Tree, tpeEnteringPosterasure: Type)(
        implicit pos: Position): js.Tree = {

      tpeEnteringPosterasure match {
        case tpe if isPrimitiveValueType(tpe) =>
          makePrimitiveUnbox(expr, tpe)

        case tpe: ErasedValueType =>
          val boxedClass = tpe.valueClazz
          val unboxMethod = boxedClass.derivedValueClassUnbox
          val content = genApplyMethod(
              genAsInstanceOf(expr, tpe),
              boxedClass, unboxMethod, Nil)
          if (unboxMethod.tpe.resultType <:< tpe.erasedUnderlying)
            content
          else
            fromAny(content, tpe.erasedUnderlying)

        case tpe =>
          genAsInstanceOf(expr, tpe)
      }
    }

    /** Gen a boxing operation (tpe is the primitive type) */
    def makePrimitiveBox(expr: js.Tree, tpe: Type)(
        implicit pos: Position): js.Tree = {
      toTypeKind(tpe) match {
        case VOID => // must be handled at least for JS interop
          js.Block(expr, js.Undefined())
        case kind: ValueTypeKind =>
          if (kind == CharKind)
            js.CallHelper("bC", expr)(encodeClassType(BoxedCharacterClass))
          else
            expr // box is identity for all non-Char types
        case _ =>
          abort(s"makePrimitiveBox requires a primitive type, found $tpe at $pos")
      }
    }

    /** Gen an unboxing operation (tpe is the primitive type) */
    def makePrimitiveUnbox(expr: js.Tree, tpe: Type)(
        implicit pos: Position): js.Tree = {
      toTypeKind(tpe) match {
        case VOID => // must be handled at least for JS interop
          /* Cast to have early typechecking errors if we use that in
           * expression position. */
          js.Cast(expr, jstpe.NoType)
        case kind: ValueTypeKind =>
          js.CallHelper("u" + kind.primitiveCharCode, expr)(toIRType(tpe))
        case _ =>
          abort(s"makePrimitiveUnbox requires a primitive type, found $tpe at $pos")
      }
    }

    private def lookupModuleClass(name: String) = {
      val module = getModuleIfDefined(name)
      if (module == NoSymbol) NoSymbol
      else module.moduleClass
    }

    lazy val ReflectArrayModuleClass = lookupModuleClass("java.lang.reflect.Array")
    lazy val UtilArraysModuleClass = lookupModuleClass("java.util.Arrays")

    /** Gen JS code for a Scala.js-specific primitive method */
    private def genJSPrimitive(tree: Apply, receiver0: Tree,
        args: List[Tree], code: Int): js.Tree = {
      import jsPrimitives._

      implicit val pos = tree.pos

      def receiver = genExpr(receiver0)
      val genArgArray = genPrimitiveJSArgs(tree.symbol, args)

      lazy val js.JSArrayConstr(genArgs) = genArgArray

      def extractFirstArg() = {
        (genArgArray: @unchecked) match {
          case js.JSArrayConstr(firstArg :: otherArgs) =>
            (firstArg, js.JSArrayConstr(otherArgs))
          case js.JSBracketMethodApply(
              js.JSArrayConstr(firstArg :: firstPart), concat, otherParts) =>
            (firstArg, js.JSBracketMethodApply(
                js.JSArrayConstr(firstPart), concat, otherParts))
        }
      }

      if (code == DYNNEW) {
        // js.Dynamic.newInstance(clazz)(actualArgs:_*)
        val (jsClass, actualArgArray) = extractFirstArg()
        actualArgArray match {
          case js.JSArrayConstr(actualArgs) =>
            js.JSNew(jsClass, actualArgs)
          case _ =>
            js.CallHelper("newInstanceWithVarargs",
                jsClass, actualArgArray)(jstpe.DynType)
        }
      } else if (code == DYNAPPLY) {
        // js.Dynamic.applyDynamic(methodName)(actualArgs:_*)
        val (methodName, actualArgArray) = extractFirstArg()
        actualArgArray match {
          case js.JSArrayConstr(actualArgs) =>
            js.JSBracketMethodApply(receiver, methodName, actualArgs)
          case _ =>
            js.CallHelper("applyMethodWithVarargs",
                receiver, methodName, actualArgArray)(jstpe.DynType)
        }
      } else if (code == DYNLITN) {
        // We have a call of the form:
        //   js.Dynamic.literal(name1 = ..., name2 = ...)
        // Translate to:
        //   {"name1": ..., "name2": ... }
        extractFirstArg() match {
          case (js.StringLiteral("apply", _),
                js.JSArrayConstr(jse.LitNamed(pairs))) =>
            js.JSObjectConstr(pairs)
          case (js.StringLiteral(name, _), _) if name != "apply" =>
            currentUnit.error(pos,
                s"js.Dynamic.literal does not have a method named $name")
            js.Undefined()
          case _ =>
            currentUnit.error(pos,
                "js.Dynamic.literal.applyDynamicNamed may not be called directly")
            js.Undefined()
        }
      } else if (code == DYNLIT) {
        // We have a call of some other form
        //   js.Dynamic.literal(...)
        // Translate to:
        //   var obj = {};
        //   obj[...] = ...;
        //   obj

        // Extract first arg to future proof against varargs
        extractFirstArg() match {
          // case js.Dynamic.literal("name1" -> ..., "name2" -> ...)
          case (js.StringLiteral("apply", _),
                js.JSArrayConstr(jse.LitNamed(pairs))) =>
            js.JSObjectConstr(pairs)
          // case js.Dynamic.literal(x, y)
          case (js.StringLiteral("apply", _),
                js.JSArrayConstr(tups)) =>

            // Create tmp variable
            val resIdent = freshLocalIdent("obj")
            val resVarDef = js.VarDef(resIdent, jstpe.DynType, mutable = false,
                js.JSObjectConstr(Nil))
            val res = js.VarRef(resIdent, mutable = false)(jstpe.DynType)

            // Assign fields
            val tuple2Type = encodeClassType(TupleClass(2))
            val assigns = tups flatMap {
              // special case for literals
              case jse.Tuple2(name, value) =>
                js.Assign(js.JSBracketSelect(res, name), value) :: Nil
              case tupExpr =>
                val tupIdent = freshLocalIdent("tup")
                val tup = js.VarRef(tupIdent, mutable = false)(tuple2Type)
                js.VarDef(tupIdent, tuple2Type, mutable = false, tupExpr) ::
                js.Assign(js.JSBracketSelect(res,
                    genApplyMethod(tup, TupleClass(2), js.Ident("$$und1__O"), Nil, jstpe.AnyType)),
                    genApplyMethod(tup, TupleClass(2), js.Ident("$$und2__O"), Nil, jstpe.AnyType)) :: Nil
            }

            js.Block(resVarDef +: assigns :+ res: _*)

          /* Here we would need the case where the varargs are passed in
           * as non-literal list:
           *   js.Dynamic.literal(x: _*)
           * However, Scala does not currently support this
           */

          // case where another method is called
          case (js.StringLiteral(name, _), _) if name != "apply" =>
            currentUnit.error(pos,
                s"js.Dynamic.literal does not have a method named $name")
            js.Undefined()
          case _ =>
            currentUnit.error(pos,
                "js.Dynamic.literal.applyDynamic may not be called directly")
            js.Undefined()
        }
      } else if (code == ARR_CREATE) {
        // js.Array.create(elements: _*)
        genArgArray
      } else if (code == ARRAYCOPY) {
        // System.arraycopy - not a helper because receiver is dropped
        js.CallHelper("systemArraycopy", genArgs)(toIRType(tree.tpe))
      } else if (code == IDHASHCODE) {
        // System.identityHashCode - not a helper because receiver is dropped
        js.CallHelper("systemIdentityHashCode", genArgs)(toIRType(tree.tpe))
      } else (genArgs match {
        case Nil =>
          code match {
            case GETGLOBAL => js.JSGlobal()
            case DEBUGGER  => js.Debugger()
            case UNDEFVAL  => js.Cast(js.Undefined(), jstpe.DynType)
            case UNITVAL   => js.Undefined()
            case UNITTYPE  => genClassConstant(UnitTpe)
            case NTR_MOD_SUFF =>
              js.StringLiteral(scala.reflect.NameTransformer.MODULE_SUFFIX_STRING)
            case NTR_NAME_JOIN =>
              js.StringLiteral(scala.reflect.NameTransformer.NAME_JOIN_STRING)
            case ENV_INFO =>
              js.CallHelper("environmentInfo")(jstpe.DynType)
          }

        case List(arg) =>

          /** Factorization of F2JS and F2JSTHIS. */
          def genFunctionToJSFunction(isThisFunction: Boolean): js.Tree = {
            val arity = {
              val funName = tree.fun.symbol.name.encoded
              assert(funName.startsWith("fromFunction"))
              funName.stripPrefix("fromFunction").toInt
            }
            val inputClass = FunctionClass(arity)
            val inputIRType = encodeClassType(inputClass)
            val applyMeth = getMemberMethod(inputClass, nme.apply) suchThat { s =>
              val ps = s.paramss
              ps.size == 1 &&
              ps.head.size == arity &&
              ps.head.forall(_.tpe.typeSymbol == ObjectClass)
            }
            val fParam = js.ParamDef(js.Ident("f"), inputIRType,
                mutable = false)
            val jsArity =
              if (isThisFunction) arity - 1
              else arity
            val jsParams = (1 to jsArity).toList map {
              x => js.ParamDef(js.Ident("arg"+x), jstpe.AnyType,
                  mutable = false)
            }
            js.Closure(
                if (isThisFunction) jstpe.AnyType else jstpe.NoType,
                fParam :: jsParams,
                jstpe.AnyType,
                genApplyMethod(
                    fParam.ref,
                    inputClass, applyMeth,
                    if (isThisFunction)
                      js.This()(jstpe.AnyType) :: jsParams.map(_.ref)
                    else
                      jsParams.map(_.ref)),
                List(arg))
          }

          code match {
            case V2JS =>
              js.Block(exprToStat(arg), js.Cast(js.Undefined(), jstpe.DynType))

            case Z2JS | N2JS | S2JS =>
              js.Cast(arg, jstpe.DynType)

            /** Convert a scala.FunctionN f to a js.FunctionN. */
            case F2JS =>
              arg match {
                /* This case will happen every time we have a Scala lambda
                 * in js.FunctionN position. We remove the JS function to
                 * Scala function wrapper, instead of adding a Scala function
                 * to JS function wrapper.
                 */
                case JSFunctionToScala(fun, arity) =>
                  fun
                case _ =>
                  genFunctionToJSFunction(isThisFunction = false)
              }

            /** Convert a scala.FunctionN f to a js.ThisFunction{N-1}. */
            case F2JSTHIS =>
              genFunctionToJSFunction(isThisFunction = true)

            case JS2Z | JS2N =>
              makePrimitiveUnbox(arg, tree.tpe)

            case JS2S =>
              genAsInstanceOf(arg, tree.tpe)

            case RTJ2J | J2RTJ =>
              arg // TODO? What if (arg === null) for RTJ2J?

            case DYNSELECT =>
              // js.Dynamic.selectDynamic(arg)
              js.JSBracketSelect(receiver, arg)

            case DICT_DEL =>
              // js.Dictionary.delete(arg)
              js.JSDelete(receiver, arg)

            case ISUNDEF =>
              // js.isUndefined(arg)
              js.BinaryOp(js.BinaryOp.===, arg, js.Undefined())
            case TYPEOF =>
              // js.typeOf(arg)
              js.UnaryOp(js.UnaryOp.typeof, arg)

            case OBJPROPS =>
              // js.Object.properties(arg)
              js.CallHelper("propertiesOf", arg)(jstpe.DynType)

            // TypedArray converters
            case AB2TA =>
              js.CallHelper("byteArray2TypedArray", arg)(jstpe.DynType)
            case AS2TA =>
              js.CallHelper("shortArray2TypedArray", arg)(jstpe.DynType)
            case AC2TA =>
              js.CallHelper("charArray2TypedArray", arg)(jstpe.DynType)
            case AI2TA =>
              js.CallHelper("intArray2TypedArray", arg)(jstpe.DynType)
            case AF2TA =>
              js.CallHelper("floatArray2TypedArray", arg)(jstpe.DynType)
            case AD2TA =>
              js.CallHelper("doubleArray2TypedArray", arg)(jstpe.DynType)

            case TA2AB =>
              js.CallHelper("typedArray2ByteArray", arg)(
                jstpe.ArrayType(encodeClassFullName(ByteClass), 1))
            case TA2AS =>
              js.CallHelper("typedArray2ShortArray", arg)(
                jstpe.ArrayType(encodeClassFullName(ShortClass), 1))
            case TA2AC =>
              js.CallHelper("typedArray2CharArray", arg)(
                jstpe.ArrayType(encodeClassFullName(CharClass), 1))
            case TA2AI =>
              js.CallHelper("typedArray2IntArray", arg)(
                jstpe.ArrayType(encodeClassFullName(IntClass), 1))
            case TA2AF =>
              js.CallHelper("typedArray2FloatArray", arg)(
                jstpe.ArrayType(encodeClassFullName(FloatClass), 1))
            case TA2AD =>
              js.CallHelper("typedArray2DoubleArray", arg)(
                jstpe.ArrayType(encodeClassFullName(DoubleClass), 1))
          }

        case List(arg1, arg2) =>
          code match {
            case DYNUPDATE =>
              // js.Dynamic.updateDynamic(arg1)(arg2)
              js.Assign(js.JSBracketSelect(receiver, arg1), arg2)

            case HASPROP =>
              // js.Object.hasProperty(arg1, arg2)
              /* Here we have an issue with evaluation order of arg1 and arg2,
               * since the obvious translation is `arg2 in arg1`, but then
               * arg2 is evaluated before arg1. Since this is not a commonly
               * used operator, we don't try to avoid unnessary temp vars, and
               * simply always evaluate arg1 in a temp before doing the `in`.
               */
              val temp = freshLocalIdent()
              js.Block(
                  js.VarDef(temp, jstpe.DynType, mutable = false, arg1),
                  js.BinaryOp(js.BinaryOp.in, arg2,
                      js.VarRef(temp, mutable = false)(jstpe.DynType)))
          }
      })
    }

    /** Gen JS code for a primitive JS call (to a method of a subclass of js.Any)
     *  This is the typed Scala.js to JS bridge feature. Basically it boils
     *  down to calling the method without name mangling. But other aspects
     *  come into play:
     *  * Operator methods are translated to JS operators (not method calls)
     *  * apply is translated as a function call, i.e. o() instead of o.apply()
     *  * Scala varargs are turned into JS varargs (see genPrimitiveJSArgs())
     *  * Getters and parameterless methods are translated as Selects
     *  * Setters are translated to Assigns of Selects
     */
    private def genPrimitiveJSCall(tree: Apply, isStat: Boolean): js.Tree = {
      implicit val pos = tree.pos

      val sym = tree.symbol
      val Apply(fun @ Select(receiver0, _), args0) = tree

      val funName = sym.unexpandedName.decoded
      val receiver = genExpr(receiver0)
      val argArray = genPrimitiveJSArgs(sym, args0)

      // valid only for methods that don't have any varargs
      lazy val js.JSArrayConstr(args) = argArray
      lazy val argc = args.length

      def hasExplicitJSEncoding =
        sym.hasAnnotation(JSNameAnnotation) ||
        sym.hasAnnotation(JSBracketAccessAnnotation)

      val boxedResult = funName match {
        case "unary_+" | "unary_-" | "unary_~" | "unary_!" =>
          assert(argc == 0)
          js.JSUnaryOp(funName.substring(funName.length-1), receiver)

        case "+" | "-" | "*" | "/" | "%" | "<<" | ">>" | ">>>" |
             "&" | "|" | "^" | "&&" | "||" | "<" | ">" | "<=" | ">=" =>
          assert(argc == 1)
          js.JSBinaryOp(funName, receiver, args.head)

        case "apply" if receiver0.tpe.typeSymbol.isSubClass(JSThisFunctionClass) =>
          js.JSBracketMethodApply(receiver, js.StringLiteral("call"), args)

        case "apply" if !hasExplicitJSEncoding =>
          argArray match {
            case js.JSArrayConstr(args) =>
              js.JSFunctionApply(receiver, args)
            case _ =>
              js.JSBracketMethodApply(
                receiver, js.StringLiteral("apply"), List(js.Null(), argArray))
          }

        case _ =>
          def jsFunName = jsNameOf(sym)

          if (sym.hasFlag(reflect.internal.Flags.DEFAULTPARAM)) {
            js.UndefinedParam()(toIRType(sym.tpe.resultType))
          } else if (jsInterop.isJSGetter(sym)) {
            assert(argc == 0)
            js.JSBracketSelect(receiver, js.StringLiteral(jsFunName))
          } else if (jsInterop.isJSSetter(sym)) {
            assert(argc == 1)
            js.Assign(
                js.JSBracketSelect(receiver,
                    js.StringLiteral(jsFunName.stripSuffix("_="))),
                args.head)
          } else if (jsInterop.isJSBracketAccess(sym)) {
            assert(argArray.isInstanceOf[js.JSArrayConstr] && (argc == 1 || argc == 2),
                s"@JSBracketAccess methods should have 1 or 2 non-varargs arguments")
            args match {
              case List(keyArg) =>
                js.JSBracketSelect(receiver, keyArg)
              case List(keyArg, valueArg) =>
                js.Assign(
                    js.JSBracketSelect(receiver, keyArg),
                    valueArg)
            }
          } else {
            argArray match {
              case js.JSArrayConstr(args) =>
                js.JSBracketMethodApply(
                    receiver, js.StringLiteral(jsFunName), args)
              case _ =>
                js.CallHelper("applyMethodWithVarargs", receiver,
                    js.StringLiteral(jsFunName), argArray)(jstpe.DynType)
            }
          }
      }

      boxedResult match {
        case js.UndefinedParam() | js.Assign(_, _) =>
          boxedResult
        case _ if isStat =>
          js.Cast(boxedResult, jstpe.NoType)
        case _ =>
          fromAny(boxedResult,
              enteringPhase(currentRun.posterasurePhase)(sym.tpe.resultType))
      }
    }

    /** Gen JS code for new java.lang.String(...)
     *  Proxies calls to method newString on object
     *  scala.scalajs.runtime.RuntimeString with proper arguments
     */
    private def genNewString(tree: Apply): js.Tree = {
      implicit val pos = tree.pos
      val Apply(fun @ Select(_, _), args0) = tree

      val ctor = fun.symbol
      val args = args0 map genExpr

      // Filter members of target module for matching member
      val compMembers = for {
        mem <- RuntimeStringModule.tpe.members
        if mem.name == jsnme.newString && ctor.tpe.matches(mem.tpe)
      } yield mem

      if (compMembers.isEmpty) {
        currentUnit.error(pos,
            s"""Could not find implementation for constructor of java.lang.String
               |with type ${ctor.tpe}. Constructors on java.lang.String
               |are forwarded to the companion object of
               |scala.scalajs.runtime.RuntimeString""".stripMargin)
        js.Undefined()
      } else {
        assert(compMembers.size == 1,
            s"""For constructor with type ${ctor.tpe} on java.lang.String,
               |found multiple companion module members.""".stripMargin)

        // Emit call to companion object
        genApplyMethod(
          genLoadModule(RuntimeStringModule),
          RuntimeStringModule.moduleClass,
          compMembers.head,
          args)
      }
    }

    /**
     * Forwards call on java.lang.String to the implementation class of
     * scala.scalajs.runtime.RuntimeString
     */
    private def genStringCall(tree: Apply): js.Tree = {
      implicit val pos = tree.pos

      val sym = tree.symbol

      // Deconstruct tree and create receiver and argument JS expressions
      val Apply(Select(receiver0, _), args0) = tree
      val receiver = js.Cast(genExpr(receiver0), jstpe.DynType)
      val args = args0 map genExpr

      // Get implementation from RuntimeString trait
      val rtStrSym = sym.overridingSymbol(RuntimeStringClass)

      // Check that we found a member
      if (rtStrSym == NoSymbol) {
        currentUnit.error(pos,
            s"""Could not find implementation for method ${sym.name}
               |on java.lang.String with type ${sym.tpe}
               |Methods on java.lang.String are forwarded to the implementation class
               |of scala.scalajs.runtime.RuntimeString""".stripMargin)
        js.Undefined()
      } else {
        assert(!rtStrSym.isOverloaded,
            s"""For method ${sym.name} on java.lang.String with type ${sym.tpe},
               |found multiple implementation class members.""".stripMargin)

        // Emit call to implementation class
        val castReceiver = js.Cast(receiver,
            toIRType(RuntimeStringClass.toTypeConstructor))
        val (implClass, methodIdent) = encodeImplClassMethodSym(rtStrSym)
        genTraitImplApply(
            encodeClassFullNameIdent(implClass),
            methodIdent,
            castReceiver :: args,
            toIRType(tree.tpe))
      }
    }

    /** Gen JS code for a new of a raw JS class (subclass of js.Any) */
    private def genPrimitiveJSNew(tree: Apply): js.Tree = {
      implicit val pos = tree.pos

      val Apply(fun @ Select(New(tpt), _), args0) = tree
      val cls = tpt.tpe.typeSymbol
      val ctor = fun.symbol

      genPrimitiveJSArgs(ctor, args0) match {
        case js.JSArrayConstr(args) =>
          if (cls == JSObjectClass && args.isEmpty) js.JSObjectConstr(Nil)
          else if (cls == JSArrayClass && args.isEmpty) js.JSArrayConstr(Nil)
          else js.JSNew(genPrimitiveJSClass(cls), args)
        case argArray =>
          js.CallHelper("newInstanceWithVarargs",
              genPrimitiveJSClass(cls), argArray)(jstpe.DynType)
      }
    }

    /** Gen JS code representing a JS class (subclass of js.Any) */
    private def genPrimitiveJSClass(sym: Symbol)(
        implicit pos: Position): js.Tree = {
      genGlobalJSObject(sym)
    }

    /** Gen JS code representing a JS module (var of the global scope) */
    private def genPrimitiveJSModule(sym: Symbol)(
        implicit pos: Position): js.Tree = {
      genGlobalJSObject(sym)
    }

    /** Gen JS code representing a JS object (class or module) in global scope
     */
    private def genGlobalJSObject(sym: Symbol)(
        implicit pos: Position): js.Tree = {
      jsNameOf(sym).split('.').foldLeft[js.Tree](js.JSGlobal()) { (memo, chunk) =>
        js.JSBracketSelect(memo, js.StringLiteral(chunk, Some(chunk)))
      }
    }

    /** Gen actual actual arguments to a primitive JS call
     *  This handles repeated arguments (varargs) by turning them into
     *  JS varargs, i.e., by expanding them into normal arguments.
     *
     *  Returns an only tree which is a JS array of the arguments. In most
     *  cases, it will be a js.JSArrayConstr with the expanded arguments. It will
     *  not if a Seq is passed to a varargs argument with the syntax seq: _*.
     */
    private def genPrimitiveJSArgs(sym: Symbol, args: List[Tree])(
        implicit pos: Position): js.Tree = {
      val wereRepeated = exitingPhase(currentRun.typerPhase) {
        for {
          params <- sym.tpe.paramss
          param <- params
        } yield isScalaRepeatedParamType(param.tpe)
      }

      var reversedParts: List[js.Tree] = Nil
      var reversedPartUnderConstruction: List[js.Tree] = Nil

      def closeReversedPartUnderConstruction() = {
        if (!reversedPartUnderConstruction.isEmpty) {
          val part = reversedPartUnderConstruction.reverse
          reversedParts ::= js.JSArrayConstr(part)
          reversedPartUnderConstruction = Nil
        }
      }

      val paramTpes = enteringPhase(currentRun.posterasurePhase) {
        for (param <- sym.tpe.params)
          yield param.tpe
      }

      for (((arg, wasRepeated), tpe) <- (args zip wereRepeated) zip paramTpes) {
        if (wasRepeated) {
          genPrimitiveJSRepeatedParam(arg) match {
            case js.JSArrayConstr(jsArgs) =>
              reversedPartUnderConstruction =
                jsArgs reverse_::: reversedPartUnderConstruction
            case jsArgArray =>
              closeReversedPartUnderConstruction()
              reversedParts ::= jsArgArray
          }
        } else {
          val unboxedArg = genExpr(arg)
          val boxedArg = unboxedArg match {
            case js.UndefinedParam() => unboxedArg
            case _                   => ensureBoxed(unboxedArg, tpe)
          }
          reversedPartUnderConstruction ::= boxedArg
        }
      }
      closeReversedPartUnderConstruction()

      // Find js.UndefinedParam at the end of the argument list. No check is
      // performed whether they may be there, since they will only be placed
      // where default arguments can be anyway
      reversedParts = reversedParts match {
        case Nil => Nil
        case js.JSArrayConstr(params) :: others =>
          val nparams =
            params.reverse.dropWhile(_.isInstanceOf[js.UndefinedParam]).reverse
          js.JSArrayConstr(nparams) :: others
        case parts => parts
      }

      // Find remaining js.UndefinedParam and replace by js.Undefined. This can
      // happen with named arguments or when multiple argument lists are present
      reversedParts = reversedParts map {
        case js.JSArrayConstr(params) =>
          val nparams = params map {
            case js.UndefinedParam() => js.Undefined()
            case param => param
          }
          js.JSArrayConstr(nparams)
        case part => part
      }

      reversedParts match {
        case Nil => js.JSArrayConstr(Nil)
        case List(part) => part
        case _ =>
          val partHead :: partTail = reversedParts.reverse
          js.JSBracketMethodApply(
              partHead, js.StringLiteral("concat"), partTail)
      }
    }

    /** Gen JS code for a repeated param of a primitive JS method
     *  In this case `arg` has type Seq[T] for some T, but the result should
     *  have type js.Array[T]. So this method takes care of the conversion.
     *  It is specialized for the shapes of tree generated by the desugaring
     *  of repeated params in Scala, so that these produce a js.JSArrayConstr.
     */
    private def genPrimitiveJSRepeatedParam(arg: Tree): js.Tree = {
      implicit val pos = arg.pos

      // Given a method `def foo(args: T*)`
      arg match {
        // foo(arg1, arg2, ..., argN) where N > 0
        case MaybeAsInstanceOf(WrapArray(
            MaybeAsInstanceOf(ArrayValue(tpt, elems)))) =>
          /* Value classes in arrays are already boxed, so no need to use
           * the type before erasure.
           */
          val elemTpe = tpt.tpe
          js.JSArrayConstr(elems.map(e => ensureBoxed(genExpr(e), elemTpe)))

        // foo()
        case Select(_, _) if arg.symbol == NilModule =>
          js.JSArrayConstr(Nil)

        // foo(argSeq:_*)
        case _ =>
          /* Here we fall back to calling runtime.genTraversableOnce2jsArray
           * to perform the conversion.
           */
          genApplyMethod(
              genLoadModule(RuntimePackageModule),
              RuntimePackageModule.moduleClass,
              Runtime_genTraversableOnce2jsArray,
              List(genExpr(arg)))
      }
    }

    object MaybeAsInstanceOf {
      def unapply(tree: Tree): Some[Tree] = tree match {
        case Apply(TypeApply(asInstanceOf_? @ Select(base, _), _), _)
        if asInstanceOf_?.symbol == Object_asInstanceOf =>
          Some(base)
        case _ =>
          Some(tree)
      }
    }

    object WrapArray {
      lazy val isWrapArray: Set[Symbol] = Seq(
          nme.wrapRefArray,
          nme.wrapByteArray,
          nme.wrapShortArray,
          nme.wrapCharArray,
          nme.wrapIntArray,
          nme.wrapLongArray,
          nme.wrapFloatArray,
          nme.wrapDoubleArray,
          nme.wrapBooleanArray,
          nme.wrapUnitArray,
          nme.genericWrapArray).map(getMemberMethod(PredefModule, _)).toSet

      def unapply(tree: Apply): Option[Tree] = tree match {
        case Apply(wrapArray_?, List(wrapped))
        if isWrapArray(wrapArray_?.symbol) =>
          Some(wrapped)
        case _ =>
          None
      }
    }

    // Synthesizers for raw JS functions ---------------------------------------

    /** Try and gen and record JS code for an anonymous function class.
     *
     *  Returns true if the class could be rewritten that way, false otherwise.
     *
     *  We make the following assumptions on the form of such classes:
     *  - It is an anonymous function
     *    - Includes being anonymous, final, and having exactly one constructor
     *  - It is not a PartialFunction
     *  - It has no field other than param accessors
     *  - It has exactly one constructor
     *  - It has exactly one non-bridge method apply if it is not specialized,
     *    or a method apply$...$sp and a forwarder apply if it is specialized.
     *  - As a precaution: it is synthetic
     *
     *  From a class looking like this:
     *
     *    final class <anon>(outer, capture1, ..., captureM) extends AbstractionFunctionN[...] {
     *      def apply(param1, ..., paramN) = {
     *        <body>
     *      }
     *    }
     *    new <anon>(o, c1, ..., cM)
     *
     *  we generate a function maker that emits:
     *
     *    lambda<o, c1, ..., cM>[notype](
     *        outer, capture1, ..., captureM, param1, ..., paramN) {
     *      <body>
     *    }
     *
     *  so that, at instantiation point, we can write:
     *
     *    new AnonFunctionN(functionMaker(this, captured1, ..., capturedM))
     *
     *  Trickier things apply when the function is specialized.
     */
    private def tryGenAndRecordAnonFunctionClass(cd: ClassDef): Boolean = {
      implicit val pos = cd.pos
      val sym = cd.symbol
      assert(sym.isAnonymousFunction,
          s"tryGenAndRecordAnonFunctionClass called with non-anonymous function $cd")

      withScopedVars(
          currentClassInfoBuilder := new ClassInfoBuilder(sym.asClass),
          currentClassSym         := sym
      ) {
        val (functionMakerBase, arity) =
          tryGenAndRecordAnonFunctionClassGeneric(cd) { msg =>
            return false
          }
        val functionMaker = { capturedArgs: List[js.Tree] =>
          JSFunctionToScala(functionMakerBase(capturedArgs), arity)
        }

        translatedAnonFunctions +=
          sym -> (functionMaker, currentClassInfoBuilder.get)
      }
      true
    }

    /** Constructor and extractor object for a tree that converts a JavaScript
     *  function into a Scala function.
     */
    private object JSFunctionToScala {
      private val AnonFunPrefScala =
        "scala.scalajs.runtime.AnonFunction"
      private val AnonFunPrefJS =
        "sjsr_AnonFunction"

      def apply(jsFunction: js.Tree, arity: Int)(
          implicit pos: Position): js.Tree = {
        val clsSym = getRequiredClass(AnonFunPrefScala + arity)
        val ctor = clsSym.tpe.member(nme.CONSTRUCTOR)
        genNew(clsSym, ctor, List(jsFunction))
      }

      def unapply(tree: js.New): Option[(js.Tree, Int)] = tree match {
        case js.New(jstpe.ClassType(wrapperName), _, List(fun))
            if wrapperName.startsWith(AnonFunPrefJS) =>
          val arityStr = wrapperName.substring(AnonFunPrefJS.length)
          try {
            Some((fun, arityStr.toInt))
          } catch {
            case e: NumberFormatException => None
          }

        case _ =>
          None
      }
    }

    /** Gen and record JS code for a raw JS function class.
     *
     *  This is called when emitting a ClassDef that represents an anonymous
     *  class extending `js.FunctionN`. These are generated by the SAM
     *  synthesizer when the target type is a `js.FunctionN`. Since JS
     *  functions are not classes, we deconstruct the ClassDef, then
     *  reconstruct it to be a genuine Closure.
     *
     *  Compared to `tryGenAndRecordAnonFunctionClass()`, this function must
     *  always succeed, because we really cannot afford keeping them as
     *  anonymous classes. The good news is that it can do so, because the
     *  body of SAM lambdas is hoisted in the enclosing class. Hence, the
     *  apply() method is just a forwarder to calling that hoisted method.
     *
     *  From a class looking like this:
     *
     *    final class <anon>(outer, capture1, ..., captureM) extends js.FunctionN[...] {
     *      def apply(param1, ..., paramN) = {
     *        outer.lambdaImpl(param1, ..., paramN, capture1, ..., captureM)
     *      }
     *    }
     *    new <anon>(o, c1, ..., cM)
     *
     *  we generate a function maker that emits:
     *
     *    lambda<o, c1, ..., cM>[notype](
     *        outer, capture1, ..., captureM, param1, ..., paramN) {
     *      outer.lambdaImpl(param1, ..., paramN, capture1, ..., captureM)
     *    }
     *
     *  The function maker is recorded in `translatedAnonFunctions` to be
     *  fetched later by the translation for New.
     */
    def genAndRecordRawJSFunctionClass(cd: ClassDef): Unit = {
      val sym = cd.symbol
      assert(isRawJSFunctionDef(sym),
          s"genAndRecordRawJSFunctionClass called with non-JS function $cd")

      withScopedVars(
          currentClassInfoBuilder := new ClassInfoBuilder(sym.asClass),
          currentClassSym         := sym
      ) {
        val (functionMaker, _) =
          tryGenAndRecordAnonFunctionClassGeneric(cd) { msg =>
            abort(s"Could not generate raw function maker for JS function: $msg")
          }

        translatedAnonFunctions +=
          sym -> (functionMaker, currentClassInfoBuilder.get)
      }
    }

    /** Code common to tryGenAndRecordAnonFunctionClass and
     *  genAndRecordRawJSFunctionClass.
     */
    private def tryGenAndRecordAnonFunctionClassGeneric(cd: ClassDef)(
        fail: (=> String) => Nothing): (List[js.Tree] => js.Tree, Int) = {
      implicit val pos = cd.pos
      val sym = cd.symbol

      // First checks

      if (sym.isSubClass(PartialFunctionClass))
        fail(s"Cannot rewrite PartialFunction $cd")
      if (instantiatedAnonFunctions contains sym) {
        // when the ordering we're given is evil (it happens!)
        fail(s"Abort function rewrite because it was already instantiated: $cd")
      }

      // First step: find the apply method def, and collect param accessors

      var paramAccessors: List[Symbol] = Nil
      var applyDef: DefDef = null

      def gen(tree: Tree): Unit = {
        tree match {
          case EmptyTree => ()
          case Template(_, _, body) => body foreach gen
          case vd @ ValDef(mods, name, tpt, rhs) =>
            val fsym = vd.symbol
            if (!fsym.isParamAccessor)
              fail(s"Found field $fsym which is not a param accessor in anon function $cd")

            if (fsym.isPrivate) {
              paramAccessors ::= fsym
            } else {
              // Uh oh ... an inner something will try to access my fields
              fail(s"Found a non-private field $fsym in $cd")
            }
          case dd: DefDef =>
            val ddsym = dd.symbol
            if (ddsym.isClassConstructor) {
              if (!ddsym.isPrimaryConstructor)
                fail(s"Non-primary constructor $ddsym in anon function $cd")
            } else {
              val name = dd.name.toString
              if (name == "apply" || (ddsym.isSpecialized && name.startsWith("apply$"))) {
                if ((applyDef eq null) || ddsym.isSpecialized)
                  applyDef = dd
              } else {
                // Found a method we cannot encode in the rewriting
                fail(s"Found a non-apply method $ddsym in $cd")
              }
            }
          case _ =>
            fail("Illegal tree in gen of genAndRecordAnonFunctionClass(): " + tree)
        }
      }
      gen(cd.impl)
      paramAccessors = paramAccessors.reverse // preserve definition order

      if (applyDef eq null)
        fail(s"Did not find any apply method in anon function $cd")

      withNewLocalNameScope {
        // Second step: build the list of useful constructor parameters

        val ctorParams = sym.primaryConstructor.tpe.params

        if (paramAccessors.size != ctorParams.size &&
            !(paramAccessors.size == ctorParams.size-1 &&
                ctorParams.head.unexpandedName == jsnme.arg_outer)) {
          fail(
              s"Have param accessors $paramAccessors but "+
              s"ctor params $ctorParams in anon function $cd")
        }

        val hasUnusedOuterCtorParam = paramAccessors.size != ctorParams.size
        val usedCtorParams =
          if (hasUnusedOuterCtorParam) ctorParams.tail
          else ctorParams
        val ctorParamDefs = usedCtorParams map { p =>
          // in the apply method's context
          js.ParamDef(encodeLocalSym(p)(p.pos), toIRType(p.tpe),
              mutable = false)(p.pos)
        }

        // Third step: emit the body of the apply method def

        val (applyMethod, methodInfoBuilder) = withScopedVars(
            paramAccessorLocals := (paramAccessors zip ctorParamDefs).toMap,
            tryingToGenMethodAsJSFunction := true
        ) {
          try {
            genMethodWithInfoBuilder(applyDef).getOrElse(
              abort(s"Oops, $applyDef did not produce a method"))
          } catch {
            case e: CancelGenMethodAsJSFunction =>
              fail(e.getMessage)
          }
        }

        withScopedVars(
            currentMethodInfoBuilder := methodInfoBuilder
        ) {
          // Fourth step: patch the body to unbox parameters and box result

          val js.MethodDef(_, params, _, body) = applyMethod
          val (patchedParams, patchedBody) =
            patchFunBodyWithBoxes(applyDef.symbol, params, body)

          // Fifth step: build the function maker

          val isThisFunction = JSThisFunctionClasses.exists(sym isSubClass _)
          assert(!isThisFunction || patchedParams.nonEmpty,
              s"Empty param list in ThisFunction: $cd")

          val functionMaker = { capturedArgs0: List[js.Tree] =>
            val capturedArgs =
              if (hasUnusedOuterCtorParam) capturedArgs0.tail
              else capturedArgs0
            assert(capturedArgs.size == ctorParamDefs.size)

            if (isThisFunction) {
              val thisParam :: actualParams = patchedParams
              js.Closure(thisParam.ptpe, ctorParamDefs ::: actualParams,
                  jstpe.AnyType,
                  js.Block(
                      js.VarDef(thisParam.name, thisParam.ptpe, mutable = false,
                          js.This()(thisParam.ptpe)(thisParam.pos))(thisParam.pos),
                      patchedBody),
                  capturedArgs)
            } else {
              js.Closure(jstpe.NoType, ctorParamDefs ::: patchedParams,
                  jstpe.AnyType, patchedBody, capturedArgs)
            }
          }

          val arity = params.size

          (functionMaker, arity)
        }
      }
    }

    /** Generate JS code for an anonymous function
     *
     *  Anonymous functions survive until the backend only under
     *  -Ydelambdafy:method
     *  and when they do, their body is always of the form
     *  EnclosingClass.this.someMethod(arg1, ..., argN, capture1, ..., captureM)
     *  where argI are the formal arguments of the lambda, and captureI are
     *  local variables or the enclosing def.
     *
     *  We translate them by instantiating scala.scalajs.runtime.AnonFunctionN
     *  with a JS closure:
     *
     *  new ScalaJS.c.sjsr_AnonFunctionN().init___xyz(
     *    lambda<this, capture1, ..., captureM>(
     *        _this, capture1, ..., captureM, arg1, ..., argN) {
     *      _this.someMethod(arg1, ..., argN, capture1, ..., captureM)
     *    }
     *  )
     *
     *  In addition, input params are unboxed before use, and the result of
     *  someMethod() is boxed back.
     */
    private def genAnonFunction(originalFunction: Function): js.Tree = {
      implicit val pos = originalFunction.pos
      val Function(paramTrees, Apply(
          targetTree @ Select(receiver, _), allArgs0)) = originalFunction

      val target = targetTree.symbol
      val params = paramTrees.map(_.symbol)

      val allArgs = allArgs0 map genExpr

      val formalArgs = params map { p =>
        js.ParamDef(encodeLocalSym(p)(p.pos), toIRType(p.tpe),
            mutable = false)(p.pos)
      }

      val isInImplClass = target.owner.isImplClass

      def makeCaptures(actualCaptures: List[js.Tree]) = {
        (actualCaptures map { c => (c: @unchecked) match {
          case js.VarRef(ident, _) =>
            (js.ParamDef(ident, c.tpe, mutable = false)(c.pos),
                js.VarRef(ident, false)(c.tpe)(c.pos))
        }}).unzip
      }

      val (allFormalCaptures, body, allActualCaptures) = if (!isInImplClass) {
        val thisActualCapture = genExpr(receiver)
        val thisFormalCapture = js.ParamDef(
            freshLocalIdent("this")(receiver.pos),
            thisActualCapture.tpe, mutable = false)(receiver.pos)
        val thisCaptureArg = thisFormalCapture.ref
        val (actualArgs, actualCaptures) = allArgs.splitAt(formalArgs.size)
        val (formalCaptures, captureArgs) = makeCaptures(actualCaptures)
        val body = genApplyMethod(thisCaptureArg, receiver.tpe, target,
            actualArgs ::: captureArgs)

        (thisFormalCapture :: formalCaptures,
            body, thisActualCapture :: actualCaptures)
      } else {
        val (thisActualCapture :: actualArgs, actualCaptures) =
          allArgs.splitAt(formalArgs.size+1)
        val (thisFormalCapture :: formalCaptures, thisCaptureArg :: captureArgs) =
          makeCaptures(thisActualCapture :: actualCaptures)
        val body = genTraitImplApply(target,
            thisCaptureArg :: actualArgs ::: captureArgs)

        (thisFormalCapture :: formalCaptures,
            body, thisActualCapture :: actualCaptures)
      }

      val (patchedFormalArgs, patchedBody) =
        patchFunBodyWithBoxes(target, formalArgs, body)
      val closure = js.Closure(
          jstpe.NoType,
          allFormalCaptures ::: patchedFormalArgs,
          jstpe.AnyType,
          patchedBody,
          allActualCaptures)

      JSFunctionToScala(closure, params.size)
    }

    private def patchFunBodyWithBoxes(methodSym: Symbol,
        params: List[js.ParamDef], body: js.Tree)(
        implicit pos: Position): (List[js.ParamDef], js.Tree) = {
      val methodType = enteringPhase(currentRun.posterasurePhase)(methodSym.tpe)

      val (paramsAny, paramsLocal) = (for {
        (param, paramSym) <- params zip methodType.params
      } yield {
        val paramTpe = enteringPhase(currentRun.posterasurePhase)(paramSym.tpe)
        val paramName = param.name
        val js.Ident(name, origName) = paramName
        val newOrigName = origName.getOrElse(name)
        val newNameIdent = freshLocalIdent(newOrigName)(paramName.pos)
        val paramAny = js.ParamDef(newNameIdent, jstpe.AnyType,
            mutable = false)(param.pos)
        val paramLocal = js.VarDef(paramName, param.ptpe, mutable = false,
            fromAny(paramAny.ref, paramTpe))
        (paramAny, paramLocal)
      }).unzip

      val patchedBody = js.Block(
          paramsLocal :+ ensureBoxed(body, methodType.resultType))

      (paramsAny, patchedBody)
    }

    // Utilities ---------------------------------------------------------------

    /** Generate a literal "zero" for the requested type */
    def genZeroOf(tpe: Type)(implicit pos: Position): js.Tree = toTypeKind(tpe) match {
      case VOID      => abort("Cannot call genZeroOf(VOID)")
      case BOOL      => js.BooleanLiteral(false)
      case LONG      => genLongImplModuleCall(jsnme.Zero)
      case INT(_)    => js.IntLiteral(0)
      case DOUBLE(_) => js.DoubleLiteral(0.0)
      case _         => js.Null()
    }

    /** Generate loading of a module value
     *  Can be given either the module symbol, or its module class symbol.
     */
    def genLoadModule(sym0: Symbol)(implicit pos: Position): js.Tree = {
      require(sym0.isModuleOrModuleClass,
          "genLoadModule called with non-module symbol: " + sym0)
      val sym1 = if (sym0.isModule) sym0.moduleClass else sym0
      val sym = // redirect all static methods of String to RuntimeString
        if (sym1 == StringModule) RuntimeStringModule.moduleClass
        else sym1

      val isGlobalScope = sym.tpe.typeSymbol isSubClass JSGlobalScopeClass

      if (isGlobalScope) js.JSGlobal()
      else if (isRawJSType(sym.tpe)) genPrimitiveJSModule(sym)
      else {
        if (!foreignIsImplClass(sym))
          currentMethodInfoBuilder.accessesModule(sym)
        js.LoadModule(jstpe.ClassType(encodeClassFullName(sym)))
      }
    }

    /** Generate a call to scala.scalajs.runtime.RuntimeLong companion */
    private def genLongModuleCall(methodName: TermName,
        args: js.Tree*)(implicit pos: Position) = {
      val LongModule = genLoadModule(RuntimeLongModule)
      val method = getMemberMethod(RuntimeLongModule, methodName)
      genApplyMethod(LongModule, RuntimeLongModule.moduleClass,
          method, args.toList)
    }

    /** Generate a call to the scala.scalajs.runtime.RuntimeLong.Impl module */
    private def genLongImplModuleCall(methodName: TermName,
        args: js.Tree*)(implicit pos: Position) = {
      val LongImplModule = genLoadModule(RuntimeLongImplModule)
      val method = getMemberMethod(RuntimeLongImplModule, methodName)
      genApplyMethod(LongImplModule, RuntimeLongImplModule.moduleClass,
          method, args.toList)
    }

    private def genOlLongCall(receiver: js.Tree, methodName: TermName,
        args: js.Tree*)(argTypes: Type*)(implicit pos: Position): js.Tree = {

      val method = getMemberMethod(RuntimeLongClass, methodName)
      assert(method.isOverloaded)

      def checkParams(types: List[Type]) =
        types.size == argTypes.size &&
        ((argTypes zip types) forall { case (t1,t2) => t1 =:= t2 })

      val opt = method.alternatives find { m =>
        checkParams(m.paramss.head.map(_.typeSignature))
      }

      genLongCall(receiver, opt.get, args: _*)
    }

    private def genLongCall(receiver: js.Tree, methodName: TermName,
        args: js.Tree*)(implicit pos: Position): js.Tree = {
      val method = getMemberMethod(RuntimeLongClass, methodName)
      genLongCall(receiver, method, args: _*)
    }

    private def genLongCall(receiver: js.Tree, method: Symbol, args: js.Tree*)(
        implicit pos: Position): js.Tree =
      genApplyMethod(receiver, RuntimeLongClass, method, args.toList)

    /** Generate access to a static member */
    private def genStaticMember(sym: Symbol)(implicit pos: Position) = {
      /* Actually, there is no static member in Scala.js. If we come here, that
       * is because we found the symbol in a Java-emitted .class in the
       * classpath. But the corresponding implementation in Scala.js will
       * actually be a val in the companion module.
       * We cannot use the .class files produced by our reimplementations of
       * these classes (in which the symbol would be a Scala accessor) because
       * that crashes the rest of scalac (at least for some choice symbols).
       * Hence we cheat here.
       */
      import scalaPrimitives._
      import jsPrimitives._
      if (isPrimitive(sym)) {
        getPrimitive(sym) match {
          case UNITVAL  => js.Undefined()
          case UNITTYPE => genClassConstant(UnitTpe)
        }
      } else {
        val instance = genLoadModule(sym.owner)
        val method = encodeStaticMemberSym(sym)
        currentMethodInfoBuilder.callsMethod(sym.owner, method)
        js.Apply(instance, method, Nil)(toIRType(sym.tpe))
      }
    }

    /** Generate a Class[_] value (e.g. coming from classOf[T]) */
    private def genClassConstant(tpe: Type)(implicit pos: Position): js.Tree = {
      val refType = toReferenceType(tpe)
      currentMethodInfoBuilder.accessesClassData(refType)
      js.ClassOf(refType)
    }
  }

  /** Tests whether the given type represents a raw JavaScript type,
   *  i.e., whether it extends scala.scalajs.js.Any.
   */
  def isRawJSType(tpe: Type): Boolean =
    tpe.typeSymbol.annotations.find(_.tpe =:= RawJSTypeAnnot.tpe).isDefined ||
    tpe.typeSymbol == UndefOrClass

  /** Test whether `sym` is the symbol of a raw JS function definition */
  private def isRawJSFunctionDef(sym: Symbol): Boolean =
    sym.isAnonymousClass && AllJSFunctionClasses.exists(sym isSubClass _)

  private def isStringType(tpe: Type): Boolean =
    tpe.typeSymbol == StringClass

  private def isLongType(tpe: Type): Boolean =
    tpe.typeSymbol == LongClass

  private lazy val BoxedBooleanClass = boxedClass(BooleanClass)
  private lazy val BoxedByteClass = boxedClass(ByteClass)
  private lazy val BoxedShortClass = boxedClass(ShortClass)
  private lazy val BoxedIntClass = boxedClass(IntClass)
  private lazy val BoxedLongClass = boxedClass(LongClass)
  private lazy val BoxedFloatClass = boxedClass(FloatClass)
  private lazy val BoxedDoubleClass = boxedClass(DoubleClass)

  private lazy val NumberClass = requiredClass[java.lang.Number]

  private lazy val HijackedNumberClasses =
    Seq(BoxedByteClass, BoxedShortClass, BoxedIntClass, BoxedLongClass,
        BoxedFloatClass, BoxedDoubleClass)
  private lazy val HijackedBoxedClasses =
    Seq(BoxedUnitClass, BoxedBooleanClass) ++ HijackedNumberClasses

  protected lazy val isHijackedBoxedClass: Set[Symbol] =
    HijackedBoxedClasses.toSet

  private lazy val InlineAnnotationClass = requiredClass[scala.inline]

  private def isMaybeJavaScriptException(tpe: Type) =
    JavaScriptExceptionClass isSubClass tpe.typeSymbol

  /** Get JS name of Symbol if it was specified with JSName annotation, or
   *  infers a default from the Scala name. */
  def jsNameOf(sym: Symbol): String =
    sym.getAnnotation(JSNameAnnotation).flatMap(_.stringArg(0)).getOrElse(
        sym.unexpandedName.decoded)

  def isStaticModule(sym: Symbol): Boolean =
    sym.isModuleClass && !sym.isImplClass && !sym.isLifted
}
