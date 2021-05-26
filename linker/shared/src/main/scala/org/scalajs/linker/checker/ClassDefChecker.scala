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

package org.scalajs.linker.checker

import scala.annotation.switch

import scala.collection.mutable

import org.scalajs.ir._
import org.scalajs.ir.Names._
import org.scalajs.ir.Trees._
import org.scalajs.ir.Types._

import org.scalajs.logging._

import org.scalajs.linker.checker.ErrorReporter._

/** Checker for the validity of the IR. */
private final class ClassDefChecker(classDef: ClassDef, reporter: ErrorReporter) {
  import ClassDefChecker._

  import reporter.reportError

  private[this] val fields =
    Array.fill(MemberNamespace.Count)(mutable.Map.empty[FieldName, Type])

  private[this] val methods =
    Array.fill(MemberNamespace.Count)(mutable.Set.empty[MethodName])

  private[this] val jsNativeMembers =
    Array.fill(MemberNamespace.Count)(mutable.Set.empty[MethodName])

  /* Per-method state (setup with withPerMethodState).
   * This state is reset per-Closure as well.
   */
  private var declaredLocalVarNamesPerMethod: mutable.Set[LocalName] = _
  private var declaredLabelNamesPerMethod: mutable.Set[LabelName] = _

  private def withPerMethodState[A](body: => A): A = {
    val savedDeclaredLocalVarNamesPerMethod = declaredLocalVarNamesPerMethod
    val savedDeclaredLabelNamesPerMethod = declaredLabelNamesPerMethod
    try {
      declaredLocalVarNamesPerMethod = mutable.Set.empty
      declaredLabelNamesPerMethod = mutable.Set.empty
      body
    } finally {
      declaredLocalVarNamesPerMethod = savedDeclaredLocalVarNamesPerMethod
      declaredLabelNamesPerMethod = savedDeclaredLabelNamesPerMethod
    }
  }

  def checkClassDef(): Unit = {
    implicit val ctx = ErrorContext(classDef)

    // `name` / `originalName` / `kind` do not need checking.

    checkJSClassCaptures(classDef.jsClassCaptures)

    checkSuperClass(classDef.superClass)

    // `interfaces` do not need checking.

    checkJSSuperClass(classDef.jsSuperClass)

    // `jsNativeLoadSpec`
    if (kindNot(ClassKind.NativeJSClass, ClassKind.NativeJSModuleClass) && classDef.jsNativeLoadSpec.isDefined)
      reportError("Non-native JS type may not have a jsNativeLoadSpec")

    classDef.memberDefs.foreach {
      case fieldDef: AnyFieldDef                => checkFieldDef(fieldDef)
      case methodDef: MethodDef                 => checkMethodDef(methodDef)
      case jsMethodDef: JSMethodDef             => checkJSMethodDef(jsMethodDef)
      case jsPropertyDef: JSPropertyDef         => checkJSPropertyDef(jsPropertyDef)
      case jsNativeMemberDef: JSNativeMemberDef => checkJSNativeMemberDef(jsNativeMemberDef)
    }

    classDef.topLevelExportDefs.foreach(checkTopLevelExportDef(_))

    if (classDef.kind == ClassKind.ModuleClass &&
        classDef.memberDefs.count(_.flags.namespace == MemberNamespace.Constructor) != 1)
      reportError("Module class must have exactly 1 constructor")
  }

  private def checkJSClassCaptures(jsClassCaptures: Option[List[ParamDef]])(
      implicit ctx: ErrorContext): Unit = {
    for (classCaptures <- jsClassCaptures) {
      if (classDef.kind != ClassKind.JSClass) {
        reportError(
            i"Class ${classDef.name} which is not a non-native JS class " +
            "cannot have class captures")
      }

      classCaptures.foldLeft(Set.empty[LocalName]) {
        case (alreadyDeclared, p @ ParamDef(ident, _, tpe, mutable)) =>
          implicit val ctx = ErrorContext(p)
          val name = ident.name
          if (alreadyDeclared(name))
            reportError(i"Duplicate JS class capture '$name'")
          if (tpe == NoType)
            reportError(i"The JS class capture $name cannot have type NoType")
          if (mutable)
            reportError(i"The JS class capture $name cannot be mutable")
          alreadyDeclared + name
      }
    }
  }

  private def checkSuperClass(superClass: Option[ClassIdent])(
      implicit ctx: ErrorContext): Unit = {
    classDef.kind match {
      case ClassKind.Class if classDef.name.name == ObjectClass =>
        if (superClass.isDefined)
          reportError("illegal superClass")

      case ClassKind.Class | ClassKind.ModuleClass | ClassKind.HijackedClass |
          ClassKind.JSClass | ClassKind.JSModuleClass |
          ClassKind.NativeJSClass | ClassKind.NativeJSModuleClass =>
        if (superClass.isEmpty)
          reportError("missing superClass")

      case ClassKind.Interface =>
        if (superClass.isDefined)
          reportError("illegal superClass")

      case ClassKind.AbstractJSType =>
        // Either is OK.
    }
  }

  private def checkJSSuperClass(jsSuperClass: Option[Tree])(
      implicit ctx: ErrorContext): Unit = {
    if (kindNot(ClassKind.JSClass, ClassKind.JSModuleClass) && jsSuperClass.isDefined)
      reportError("Only non-native JS types may have a jsSuperClass")

    jsSuperClass.foreach(checkTree(_, Env.fromParams(classDef.jsClassCaptures.getOrElse(Nil))))
  }

  private def checkFieldDef(fieldDef: AnyFieldDef): Unit = {
    implicit val ctx = ErrorContext(fieldDef)

    if (fieldDef.flags.namespace.isPrivate)
      reportError("A field cannot be private")
    if (fieldDef.flags.namespace.isConstructor)
      reportError("A field cannot be a constuctor")

    fieldDef match {
      case FieldDef(_, FieldIdent(name), _, ftpe) =>
        if (kindNot(ClassKind.Class, ClassKind.ModuleClass, ClassKind.JSClass, ClassKind.JSModuleClass))
          reportError("illegal FieldDef")
        if (fields(fieldDef.flags.namespace.ordinal).put(name, ftpe).isDefined)
          reportError(i"duplicate field $name")

      case JSFieldDef(_, name, _) =>
        if (kindNot(ClassKind.JSClass, ClassKind.JSModuleClass))
          reportError("illegal JSFieldDef")
        checkTree(name, Env.empty)
    }

    if (fieldDef.ftpe == NoType || fieldDef.ftpe == NothingType)
      reportError(i"FieldDef cannot have type ${fieldDef.ftpe}")
  }

  private def checkMethodDef(methodDef: MethodDef): Unit = withPerMethodState {
    val MethodDef(flags, MethodIdent(name), _, params, _, body) = methodDef
    implicit val ctx = ErrorContext(methodDef)

    val namespace = flags.namespace
    val static = namespace.isStatic
    val isConstructor = namespace == MemberNamespace.Constructor

    if (flags.isMutable)
      reportError("A method cannot have the flag Mutable")

    checkMethodNameNamespace(name, namespace)

    if (!methods(namespace.ordinal).add(name))
      reportError(i"duplicate method def $name")

    // ClassInitializer
    if (name.isClassInitializer) {
      if (!classDef.kind.isJSClass) {
        reportError(
            i"The non JS class ${classDef.name} cannot have a class " +
            "initializer")
      }

      if (classDef.jsClassCaptures.isDefined) {
        reportError(
            i"The non-top-level JS class ${classDef.name} cannot have a " +
            "class initializer")
      }
    }

    classDef.kind match {
      case ClassKind.JSClass | ClassKind.JSModuleClass =>
        if (!static)
          reportError("Non exported instance method is illegal in JS class")

      case ClassKind.ModuleClass =>
        if (isConstructor && name != NoArgConstructorName)
          reportError("Module class must have a parameterless constructor")

      case ClassKind.Class | ClassKind.HijackedClass =>
        // all namespaces are allowed (except for class initializers as checked above)

      case ClassKind.Interface =>
        if (isConstructor)
          reportError("Interfaces cannot declare constructors")

      case ClassKind.NativeJSClass | ClassKind.NativeJSModuleClass | ClassKind.AbstractJSType =>
        if (!static)
          reportError("illegal instance member")
    }


    // Params
    for (ParamDef(name, _, tpe, _) <- params) {
      checkDeclareLocalVar(name)
      if (tpe == NoType)
        reportError(i"Parameter $name has type NoType")
    }

    // Body
    body.foreach(checkTree(_, Env.fromParams(params)))
  }

  private def checkJSMethodDef(methodDef: JSMethodDef): Unit = withPerMethodState {
    val JSMethodDef(flags, pName, params, restParam, body) = methodDef
    implicit val ctx = ErrorContext(methodDef)

    val static = flags.namespace.isStatic

    if (flags.isMutable)
      reportError("An exported method cannot have the flag Mutable")
    if (flags.namespace.isPrivate)
      reportError("An exported method cannot be private")
    if (flags.namespace.isConstructor)
      reportError("An exported method cannot be in the constructor namespace")

    if (kindNot(ClassKind.Class, ClassKind.ModuleClass, ClassKind.JSClass, ClassKind.JSModuleClass))
      reportError("Exported method def can only appear in a class")
    else if (static && classDef.kind != ClassKind.JSClass)
      reportError("Exported method def in non-JS class cannot be static")

    checkExportedPropertyName(pName)
    checkJSParamDefs(params, restParam)
    checkTree(body, Env.fromParams(classDef.jsClassCaptures.getOrElse(Nil) ++ params ++ restParam))
  }

  private def checkJSPropertyDef(propDef: JSPropertyDef): Unit = {
    val JSPropertyDef(flags, pName, getterBody, setterArgAndBody) = propDef
    implicit val ctx = ErrorContext(propDef)

    val static = flags.namespace.isStatic

    if (flags.isMutable)
      reportError("An exported property def cannot have the flag Mutable")
    if (flags.namespace.isPrivate)
      reportError("An exported property def cannot be private")
    if (flags.namespace.isConstructor)
      reportError("An exported property def cannot be in the constructor namespace")

    if (kindNot(ClassKind.Class, ClassKind.ModuleClass, ClassKind.JSClass, ClassKind.JSModuleClass))
      reportError("Exported property def can only appear in a class")

    checkExportedPropertyName(pName)

    getterBody.foreach { body =>
      withPerMethodState {
        checkTree(body, Env.fromParams(classDef.jsClassCaptures.getOrElse(Nil)))
      }
    }

    setterArgAndBody.foreach { case (setterArg, body) =>
      withPerMethodState {
        checkJSParamDefs(setterArg :: Nil, None)
        checkTree(body, Env.fromParams(classDef.jsClassCaptures.getOrElse(Nil) :+ setterArg))
      }
    }
  }

  private def checkJSNativeMemberDef(jsNativeMemberDef: JSNativeMemberDef): Unit = {
    val JSNativeMemberDef(flags, MethodIdent(name), _) = jsNativeMemberDef
    implicit val ctx = ErrorContext(jsNativeMemberDef)

    val namespace = flags.namespace

    if (flags.isMutable)
      reportError("A js native def cannot have the flag Mutable")
    if (namespace != MemberNamespace.PublicStatic)
      reportError("A js native def must be in the public static namespace")

    checkMethodNameNamespace(name, namespace)

    if (!jsNativeMembers(namespace.ordinal).add(name))
      reportError(i"duplicate js native member def $name")
  }

  private def checkExportedPropertyName(propName: Tree)(
      implicit ctx: ErrorContext): Unit = {
    if (kindNot(ClassKind.JSClass, ClassKind.JSModuleClass)) {
      propName match {
        case StringLiteral(name) =>
          if (name.contains("__"))
            reportError("Exported method def name cannot contain __")

        case _ =>
          reportError("Only JS classes may contain members with computed names")
      }
    }
  }

  private def checkTopLevelExportDef(topLevelExportDef: TopLevelExportDef): Unit = {
    implicit val ctx = ErrorContext(topLevelExportDef)

    topLevelExportDef match {
      case _: TopLevelJSClassExportDef =>
        if (classDef.kind != ClassKind.JSClass)
          reportError("Exported JS class def can only appear in a JS class")

      case _: TopLevelModuleExportDef =>
        if (!classDef.kind.hasModuleAccessor)
          reportError("Top-level module export def can only appear in a module class")

      case TopLevelMethodExportDef(_, methodDef) =>
        checkTopLevelMethodExportDef(methodDef)

      case topLevelExportDef: TopLevelFieldExportDef =>
        checkTopLevelFieldExportDef(topLevelExportDef)
    }
  }

  private def checkTopLevelMethodExportDef(methodDef: JSMethodDef): Unit = withPerMethodState {
    val JSMethodDef(flags, pName, params,  restParam, body) = methodDef
    implicit val ctx = ErrorContext(methodDef)

    if (flags.isMutable)
      reportError("Top level export method cannot have the flag Mutable")
    if (flags.namespace != MemberNamespace.PublicStatic)
      reportError("Top level export must be public and static")

    if (!pName.isInstanceOf[StringLiteral])
      reportError("Top level exports may not have computed names")

    checkJSParamDefs(params, restParam)
    checkTree(body, Env.fromParams(params ++ restParam))
  }

  private def checkTopLevelFieldExportDef(
      topLevelFieldExportDef: TopLevelFieldExportDef): Unit = {
    implicit val ctx = ErrorContext(topLevelFieldExportDef)

    if (kindNot(ClassKind.Class, ClassKind.ModuleClass, ClassKind.JSClass, ClassKind.JSModuleClass))
      reportError("native classes may not have field exports")

    val field = topLevelFieldExportDef.field

    fields(MemberNamespace.PublicStatic.ordinal).get(field.name).fold {
      reportError(i"Cannot export non-existent static field '$field'")
    } { tpe =>
      if (tpe != AnyType)
        reportError(i"Cannot export field '$field' of type $tpe")
    }
  }

  private def checkMethodNameNamespace(name: MethodName, namespace: MemberNamespace)(
      implicit ctx: ErrorContext): Unit = {
    if (name.isReflectiveProxy && namespace != MemberNamespace.Public)
      reportError("reflective proxies must be in the public (non-static) namespace")

    if (name.isConstructor != (namespace == MemberNamespace.Constructor))
      reportError("a member can have a constructor name iff it is in the constructor namespace")

    if ((name.isStaticInitializer || name.isClassInitializer) != (namespace == MemberNamespace.StaticConstructor))
      reportError("a member can have a static constructor name iff it is in the static constructor namespace")
  }

  private def checkJSParamDefs(params: List[ParamDef], restParam: Option[ParamDef])(
      implicit ctx: ErrorContext): Unit = {
    for (ParamDef(name, _, ptpe, _) <- params ++ restParam) {
      checkDeclareLocalVar(name)
      if (ptpe != AnyType)
        reportError(i"Parameter $name has type $ptpe but must be any")
    }
  }

  private def checkTreeOrSpreads(trees: List[TreeOrJSSpread], env: Env): Unit = {
    trees.foreach {
      case JSSpread(items) => checkTree(items, env)
      case tree: Tree      => checkTree(tree, env)
    }
  }

  private def checkTrees(trees: List[Tree], env: Env): Unit =
    trees.foreach(checkTree(_, env))

  private def checkTree(tree: Tree, env: Env): Env = {
    implicit val ctx = ErrorContext(tree)

    def checkApplyGeneric(methodName: MethodName, args: List[Tree]): Unit = {
      val paramRefs = methodName.paramTypeRefs.size
      if (args.size != paramRefs)
        reportError(i"Arity mismatch: $paramRefs expected but "+
            i"${args.size} found")
      checkTrees(args, env)
    }

    tree match {
      case VarDef(ident, _, vtpe, mutable, rhs) =>
        checkDeclareLocalVar(ident)
        checkTree(rhs, env)
        env.withLocal(LocalDef(ident.name, vtpe, mutable))

      case Skip() =>
        env

      case Assign(lhs, rhs) =>
        lhs match {
          case VarRef(LocalIdent(name)) =>
            if (!env.locals(name).mutable)
              reportError(i"Assignment to immutable variable $name.")

          case _: Select | _: JSPrivateSelect | _: SelectStatic |
              _:ArraySelect | _:RecordSelect | _:JSSelect | _:JSSuperSelect |
              _:JSGlobalRef =>
        }
        checkTree(lhs, env)
        checkTree(rhs, env)
        env

      case StoreModule(_, value) =>
        checkTree(value, env)
        env

      case Block(stats) =>
        stats.foldLeft(env) { (prevEnv, stat) =>
          checkTree(stat, prevEnv)
        }
        env

      case Labeled(label, _, body) =>
        checkDeclareLabel(label)
        checkTree(body, env.withLabel(label.name))
        env

      case If(cond, thenp, elsep) =>
        checkTree(cond, env)
        checkTree(thenp, env)
        checkTree(elsep, env)
        env

      case While(cond, body) =>
        checkTree(cond, env)
        checkTree(body, env)
        env

      case DoWhile(body, cond) =>
        checkTree(body, env)
        checkTree(cond, env)
        env

      case ForIn(obj, keyVar, _, body) =>
        checkTree(obj, env)
        val bodyEnv =
          env.withLocal(LocalDef(keyVar.name, AnyType, false))
        checkTree(body, bodyEnv)
        env

      case TryCatch(block, errVar, _, handler) =>
        checkTree(block, env)
        val handlerEnv =
          env.withLocal(LocalDef(errVar.name, AnyType, false))
        checkTree(handler, handlerEnv)
        env

      case TryFinally(block, finalizer) =>
        checkTree(block, env)
        checkTree(finalizer, env)
        env

      case Match(selector, cases, default) =>
        checkTree(selector, env)
        for ((alts, body) <- cases) {
          checkTrees(alts, env)
          checkTree(body, env)
        }

        checkTree(default, env)

        env

      case Debugger() =>
        env

      case JSDelete(qualifier, item) =>
        checkTree(qualifier, env)
        checkTree(item, env)
        env

      case Return(expr, label) =>
        if (!env.returnLabels.contains(label.name))
          reportError(i"unknown label $label.")

        checkTree(expr, env)
        env

      case Throw(expr) =>
        checkTree(expr, env)
        env

      // Scala expressions

      case New(_, ctor, args) =>
        checkApplyGeneric(ctor.name, args)
        env

      case _: LoadModule =>
        env

      case Select(qualifier, _, _) =>
        checkTree(qualifier, env)
        env

      case _: SelectStatic =>
        env

      case _: SelectJSNativeMember =>
        env

      case Apply(flags, receiver, MethodIdent(method), args) =>
        if (flags.isPrivate)
          reportError("Illegal flag for Apply: Private")
        checkTree(receiver, env)
        checkApplyGeneric(method, args)
        env

      case ApplyStatically(_, receiver, _, MethodIdent(method), args) =>
        checkTree(receiver, env)
        checkApplyGeneric(method, args)
        env

      case ApplyStatic(_, _, MethodIdent(method), args) =>
        checkApplyGeneric(method, args)
        env

      case ApplyDynamicImport(_, className, MethodIdent(method), args) =>
        checkApplyGeneric(method, args)
        env

      case UnaryOp(_, lhs) =>
        checkTree(lhs, env)
        env

      case BinaryOp(_, lhs, rhs) =>
        checkTree(lhs, env)
        checkTree(rhs, env)
        env

      case NewArray(typeRef, lengths) =>
        if (lengths.isEmpty)
          reportError("NewArray must have non-0 dimensions")
        checkArrayTypeRef(typeRef)
        checkTrees(lengths, env)
        env

      case ArrayValue(typeRef, elems) =>
        checkArrayTypeRef(typeRef)
        checkTrees(elems, env)
        env

      case ArrayLength(array) =>
        if (!array.tpe.isInstanceOf[ArrayType])
          reportError(i"Array type expected but ${array.tpe} found")
        checkTree(array, env)
        env

      case ArraySelect(array, index) =>
        if (!array.tpe.isInstanceOf[ArrayType])
          reportError(i"Array type expected but ${array.tpe} found")
        checkTree(index, env)
        env

      case IsInstanceOf(expr, testType) =>
        checkTree(expr, env)
        checkIsAsInstanceTargetType(testType)
        env

      case AsInstanceOf(expr, tpe) =>
        checkTree(expr, env)
        checkIsAsInstanceTargetType(tpe)
        env

      case GetClass(expr) =>
        checkTree(expr, env)
        env

      case Clone(expr) =>
        checkTree(expr, env)
        env

      case IdentityHashCode(expr) =>
        checkTree(expr, env)
        env

      // JavaScript expressions

      case JSNew(ctor, args) =>
        checkTree(ctor, env)
        checkTreeOrSpreads(args, env)
        env

      case JSPrivateSelect(qualifier, className, field) =>
        checkTree(qualifier, env)
        env

      case JSSelect(qualifier, item) =>
        checkTree(qualifier, env)
        checkTree(item, env)
        env

      case JSFunctionApply(fun, args) =>
        checkTree(fun, env)
        checkTreeOrSpreads(args, env)
        env

      case JSMethodApply(receiver, method, args) =>
        checkTree(receiver, env)
        checkTree(method, env)
        checkTreeOrSpreads(args, env)
        env

      case JSSuperSelect(superClass, qualifier, item) =>
        checkTree(superClass, env)
        checkTree(qualifier, env)
        checkTree(item, env)
        env

      case JSSuperMethodCall(superClass, receiver, method, args) =>
        checkTree(superClass, env)
        checkTree(receiver, env)
        checkTree(method, env)
        checkTreeOrSpreads(args, env)
        env

      case JSSuperConstructorCall(args) =>
        checkTreeOrSpreads(args, env)
        env

      case JSImportCall(arg) =>
        checkTree(arg, env)
        env

      case LoadJSConstructor(_) =>
        env

      case LoadJSModule(_) =>
        env

      case JSUnaryOp(_, lhs) =>
        checkTree(lhs, env)
        env

      case JSBinaryOp(_, lhs, rhs) =>
        checkTree(lhs, env)
        checkTree(rhs, env)
        env

      case JSArrayConstr(items) =>
        checkTreeOrSpreads(items, env)
        env

      case JSObjectConstr(fields) =>
        for ((key, value) <- fields) {
          checkTree(key, env)
          checkTree(value, env)
        }
        env

      case JSGlobalRef(_) =>
        env

      case JSTypeOfGlobalRef(_) =>
        env

      case JSLinkingInfo() =>
        env

      // Literals

      case ClassOf(typeRef) =>
        typeRef match {
          case NullRef | NothingRef =>
            reportError(i"Invalid classOf[$typeRef]")
          case typeRef: ArrayTypeRef =>
            checkArrayTypeRef(typeRef)
          case _ =>
            // ok
        }
        env

      case _: Literal =>
        env

      // Atomic expressions

      case VarRef(LocalIdent(name)) =>
        env.locals.get(name).fold[Unit] {
          reportError(i"Cannot find variable $name in scope")
        } { localDef =>
          if (tree.tpe != localDef.tpe)
            reportError(i"Variable $name of type ${localDef.tpe} "+
                i"typed as ${tree.tpe}")
        }
        env

      case This() =>
        env

      case Closure(arrow, captureParams, params, restParam, body, captureValues) =>
        /* Check compliance of captureValues wrt. captureParams in the current
         * method state, i.e., outside `withPerMethodState`.
         */
        if (captureParams.size != captureValues.size)
          reportError("Mismatched size for captures: "+
              i"${captureParams.size} params vs ${captureValues.size} values")

        checkTrees(captureValues, env)

        // Then check the closure params and body in its own per-method state
        withPerMethodState {
          for (ParamDef(name, _, ctpe, mutable) <- captureParams) {
            checkDeclareLocalVar(name)
            if (mutable)
              reportError(i"Capture parameter $name cannot be mutable")
            if (ctpe == NoType)
              reportError(i"Parameter $name has type NoType")
          }

          checkJSParamDefs(params, restParam)

          val thisType = if (arrow) NoType else AnyType
          val bodyEnv = Env.fromParams(captureParams ++ params ++ restParam)
          checkTree(body, bodyEnv)
        }
        env

      case CreateJSClass(className, captureValues) =>
        checkTrees(captureValues, env)
        env

      case RecordValue(tpe, elems) =>
        checkTrees(elems, env)
        // TODO check tpe / elems count
        env

      case RecordSelect(record, field) =>
        // TODO check record has field
        checkTree(record, env)
        env

      case _: Transient =>
        env
    }
  }

  private def checkIsAsInstanceTargetType(tpe: Type)(
      implicit ctx: ErrorContext): Unit = {
    tpe match {
      case NoType | NullType | NothingType | _:RecordType =>
        reportError(i"$tpe is not a valid target type for Is/AsInstanceOf")

      case tpe: ArrayType =>
        checkArrayType(tpe)

      case _ =>
        // ok
    }
  }

  private def checkArrayType(tpe: ArrayType)(
      implicit ctx: ErrorContext): Unit = {
    checkArrayTypeRef(tpe.arrayTypeRef)
  }

  private def checkArrayTypeRef(typeRef: ArrayTypeRef)(
      implicit ctx: ErrorContext): Unit = {
    typeRef.base match {
      case VoidRef | NullRef | NothingRef =>
        reportError(i"Invalid array type $typeRef")
      case _ =>
        // ok
    }
  }

  private def checkDeclareLocalVar(ident: LocalIdent)(
      implicit ctx: ErrorContext): Unit = {
    if (!declaredLocalVarNamesPerMethod.add(ident.name))
      reportError(i"Duplicate local variable name ${ident.name}.")
  }

  private def checkDeclareLabel(label: LabelIdent)(
      implicit ctx: ErrorContext): Unit = {
    if (!declaredLabelNamesPerMethod.add(label.name))
      reportError(i"Duplicate label named ${label.name}.")
  }

  private def kindNot(kinds: ClassKind*): Boolean =
    !kinds.contains(classDef.kind)
}

object ClassDefChecker {
  /** Checks that the IR in a [[ClassDef]] is correct.
   *
   *  @return Count of IR checking errors (0 in case of success)
   */
  def check(classDef: ClassDef, logger: Logger): Int = {
    val reporter = new ErrorReporter(logger)
    new ClassDefChecker(classDef, reporter).checkClassDef()
    reporter.errorCount
  }

  private class Env(
      /** Local variables in scope (including through closures). */
      val locals: Map[LocalName, LocalDef],
      /** Return types by label. */
      val returnLabels: Set[LabelName],
  ) {
    import Env._

    def withLocal(localDef: LocalDef)(implicit ctx: ErrorContext): Env =
      new Env(locals + (localDef.name -> localDef), returnLabels)

    def withLabel(label: LabelName): Env =
      new Env(locals, returnLabels + label)
  }

  private object Env {
    val empty: Env = new Env(Map.empty, Set.empty)

    def fromParams(params: List[ParamDef]): Env = {
      val paramLocalDefs =
        for (p @ ParamDef(ident, _, tpe, mutable) <- params)
          yield ident.name -> LocalDef(ident.name, tpe, mutable)
      new Env(paramLocalDefs.toMap, Set.empty)
    }
  }

  private final case class LocalDef(name: LocalName, tpe: Type,
      mutable: Boolean)
}
