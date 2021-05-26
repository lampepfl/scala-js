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

// In the IR checker, we allow early returns for improved readability
// scalastyle:off return

import scala.annotation.switch

import scala.collection.mutable

import org.scalajs.ir._
import org.scalajs.ir.Names._
import org.scalajs.ir.Trees._
import org.scalajs.ir.Types._

import org.scalajs.logging._

import org.scalajs.linker.frontend.LinkingUnit
import org.scalajs.linker.standard.LinkedClass
import org.scalajs.linker.checker.ErrorReporter._

/** Checker for the validity of the IR. */
private final class IRChecker(unit: LinkingUnit, reporter: ErrorReporter) {

  import reporter.reportError

  private val classes: mutable.Map[ClassName, CheckedClass] = {
    val tups = for (classDef <- unit.classDefs) yield {
      implicit val ctx = ErrorContext(classDef)
      val c = new CheckedClass(classDef)
      c.name -> c
    }
    mutable.Map(tups: _*)
  }

  def check(): Unit = {
    for (classDef <- unit.classDefs) {
      implicit val ctx = ErrorContext(classDef)

      checkJSSuperClass(classDef)
      checkStaticMembers(classDef)

      classDef.kind match {
        case ClassKind.AbstractJSType | ClassKind.NativeJSClass |
            ClassKind.NativeJSModuleClass =>
          if (classDef.fields.nonEmpty ||
              classDef.methods.exists(!_.value.flags.namespace.isStatic) ||
              classDef.exportedMembers.nonEmpty) {
            val kind =
              if (classDef.kind == ClassKind.AbstractJSType) "Abstract"
              else "Native"
            reportError(
                i"$kind JS type ${classDef.name} cannot have instance members")
          }
        case _ =>
          checkScalaClassDef(classDef)
      }
    }

    for (topLevelExport <- unit.topLevelExports) {
      val owningClass = topLevelExport.owningClass

      topLevelExport.tree match {
        case tree: TopLevelJSClassExportDef =>

        case tree: TopLevelModuleExportDef =>

        case tree: TopLevelMethodExportDef =>
          checkTopLevelMethodExportDef(tree)

        case tree: TopLevelFieldExportDef =>
      }
    }
  }


  private def checkJSSuperClass(classDef: LinkedClass): Unit = {
    implicit val ctx = ErrorContext(classDef)

    if (classDef.kind.isJSClass) {
      classDef.jsSuperClass.fold {
        // .get is OK: the Analyzer checks that a super class is present.
        val superClass = lookupClass(classDef.superClass.get.name)
        if (superClass.jsClassCaptures.isDefined)
          reportError(i"super class ${superClass.name} may not have jsClassCaptures")
        else if (superClass.kind == ClassKind.NativeJSClass && superClass.jsNativeLoadSpec.isEmpty)
          reportError(i"Native super class ${superClass.name} must have a native load spec")
      } { tree =>
        typecheckExpect(tree, Env.empty, AnyType)
      }
    } else {
      if (classDef.jsSuperClass.isDefined)
        reportError("Only non-native JS types may have a jsSuperClass")
    }
  }

  private def checkStaticMembers(classDef: LinkedClass): Unit = {
    for {
      member <- classDef.methods
      if member.value.flags.namespace.isStatic
    } {
      val methodDef = member.value
      implicit val ctx = ErrorContext(methodDef)

      checkMethodDef(methodDef, classDef)
    }
  }

  private def checkScalaClassDef(classDef: LinkedClass): Unit = {
    assert(classDef.kind != ClassKind.AbstractJSType &&
        classDef.kind != ClassKind.NativeJSClass &&
        classDef.kind != ClassKind.NativeJSModuleClass)

    // Is this a normal class?
    if (classDef.kind != ClassKind.HijackedClass &&
        classDef.kind != ClassKind.Interface) {
      // Check fields
      checkFieldDefs(classDef)

      // Module classes must have exactly one constructor, without parameter
      if (classDef.kind == ClassKind.ModuleClass) {
        implicit val ctx = ErrorContext(classDef)
        val methods = classDef.methods
        if (methods.count(m => m.value.flags.namespace == MemberNamespace.Constructor) != 1)
          reportError("Module class must have exactly 1 constructor")
        if (!methods.exists(_.value.methodName == NoArgConstructorName))
          reportError("Module class must have a parameterless constructor")
      }

      val checkedClass = classes(classDef.name.name)

      // Check exported members
      for (member <- classDef.exportedMembers) {
        implicit val ctx = ErrorContext(member.value)

        member.value match {
          case m: JSMethodDef =>
            checkExportedMethodDef(m, checkedClass)

          case p: JSPropertyDef =>
            checkExportedPropertyDef(p, checkedClass)

          // Anything else is illegal
          case _ =>
            reportError("Illegal exported class member of type " +
                member.value.getClass.getName)
        }
      }
    } else {
      implicit val ctx = ErrorContext(classDef)

      def kindStr =
        if (classDef.kind == ClassKind.HijackedClass) "Hijacked classes"
        else "Interfaces"

      if (classDef.fields.nonEmpty)
        reportError(i"$kindStr may not have fields")

      if (classDef.exportedMembers.nonEmpty)
        reportError(i"$kindStr may not have exports")
    }

    // Check methods
    for {
      method <- classDef.methods
      if !method.value.flags.namespace.isStatic
    } {
      val tree = method.value
      implicit val ctx = ErrorContext(tree)

      checkMethodDef(tree, classDef)
    }
  }

  private def checkFieldDefs(classDef: LinkedClass): Unit = {
    for (fieldDef <- classDef.fields)
      checkFieldDef(fieldDef, classDef)
  }

  private def checkFieldDef(fieldDef: AnyFieldDef, classDef: LinkedClass): Unit = {
    implicit val ctx = ErrorContext(fieldDef)

    if (fieldDef.flags.namespace.isPrivate)
      reportError("A field cannot be private")

    fieldDef match {
      case _: FieldDef =>
        // ok
      case JSFieldDef(_, name, _) =>
        if (!classDef.kind.isJSClass)
          reportError(i"Illegal JS field '$name' in Scala class")
        typecheckExpect(name, Env.empty, AnyType)
    }

    if (fieldDef.ftpe == NoType || fieldDef.ftpe == NothingType)
      reportError(i"FieldDef cannot have type ${fieldDef.ftpe}")
  }

  private def checkMethodDef(methodDef: MethodDef,
      classDef: LinkedClass): Unit =  {

    val MethodDef(flags, MethodIdent(name), _, params, resultType, body) =
      methodDef
    implicit val ctx = ErrorContext(methodDef)

    val namespace = flags.namespace
    val static = namespace.isStatic
    val isConstructor = namespace == MemberNamespace.Constructor

    if (flags.isMutable)
      reportError("A method cannot have the flag Mutable")

    if (classDef.kind.isJSClass && !static) {
      reportError(i"Non exported instance method $name is illegal in JS class")
      return // things would go too badly otherwise
    }

    if (isConstructor && classDef.kind == ClassKind.Interface)
      reportError("Interfaces cannot declare constructors")
    if (isConstructor != name.isConstructor)
      reportError("A method must have a constructor name iff it is a constructor")

    val hasStaticConstructorName = name.isStaticInitializer || name.isClassInitializer
    if ((namespace == MemberNamespace.StaticConstructor) != hasStaticConstructorName)
      reportError("A method must have a static constructor name iff it is a static constructor")

    val advertizedSig = (params.map(_.ptpe), resultType)
    val sigFromName = inferMethodType(name, static)
    if (advertizedSig != sigFromName) {
      reportError(
          i"The signature of ${classDef.name.name}.$name, which is "+
          i"$advertizedSig, does not match its name (should be $sigFromName).")
    }

    // Compute bodyEnv even for abstract defs for error checking in fromSignature
    val thisType =
      if (static) NoType
      else ClassType(classDef.name.name)
    val bodyEnv = {
      val inConstructorOf =
        if (isConstructor) Some(classDef.name.name)
        else None
      Env.fromSignature(thisType, inConstructorOf)
    }

    body.fold {
      // Abstract
      reportError(
          i"The abstract method ${classDef.name.name}.$name survived the " +
          "Analyzer (this is a bug)")
    } { body =>
      // Concrete
      if (resultType == NoType)
        typecheckStat(body, bodyEnv)
      else
        typecheckExpect(body, bodyEnv, resultType)
    }
  }

  private def checkExportedMethodDef(methodDef: JSMethodDef,
      clazz: CheckedClass): Unit =  {
    val JSMethodDef(flags, pName, params, restParam, body) = methodDef
    implicit val ctx = ErrorContext(methodDef)

    val static = flags.namespace.isStatic

    if (flags.isMutable)
      reportError("An exported method cannot have the flag Mutable")
    if (flags.namespace.isPrivate)
      reportError("An exported method cannot be private")

    if (!clazz.kind.isAnyNonNativeClass) {
      reportError(i"Exported method def can only appear in a class")
      return
    }

    if (static && clazz.kind != ClassKind.JSClass)
      reportError("Exported method def in non-JS class cannot be static")

    checkExportedPropertyName(pName, clazz)

    def isJSConstructor = {
      !static && (pName match {
        case StringLiteral("constructor") => true
        case _                            => false
      })
    }

    if (clazz.kind.isJSClass && isJSConstructor) {
      checkJSClassConstructor(methodDef, clazz)
    } else {
      val thisType = {
        if (static) NoType
        else if (clazz.kind.isJSClass) AnyType
        else ClassType(clazz.name)
      }

      val bodyEnv = Env.fromSignature(thisType)
      typecheckExpect(body, bodyEnv, AnyType)
    }
  }

  private def checkJSClassConstructor(methodDef: JSMethodDef,
      clazz: CheckedClass): Unit = {
    val JSMethodDef(static, _, params, restParam, body) = methodDef
    implicit val ctx = ErrorContext(methodDef)

    val bodyStats = body match {
      case Block(stats) => stats
      case _            => body :: Nil
    }

    val (prepStats, superCallAndRest) =
      bodyStats.span(!_.isInstanceOf[JSSuperConstructorCall])

    val (superCall, restStats) = superCallAndRest match {
      case (superCall: JSSuperConstructorCall) :: restStats =>
        (superCall, restStats)
      case _ =>
        reportError(
            "A JS class constructor must contain one super constructor " +
            "call at the top-level")
        (JSSuperConstructorCall(Nil)(methodDef.pos), Nil)
    }

    val initialEnv = Env.fromSignature(NoType, inConstructorOf = Some(clazz.name))

    val preparedEnv = prepStats.foldLeft(initialEnv) { (prevEnv, stat) =>
      typecheckStat(stat, prevEnv)
    }

    for (arg <- superCall.args)
      typecheckExprOrSpread(arg, preparedEnv)

    val restEnv = preparedEnv.withThis(AnyType)
    typecheckStat(Block(restStats)(methodDef.pos), restEnv)
  }

  private def checkExportedPropertyDef(propDef: JSPropertyDef,
      clazz: CheckedClass): Unit =  {
    val JSPropertyDef(flags, pName, getterBody, setterArgAndBody) = propDef
    implicit val ctx = ErrorContext(propDef)

    val static = flags.namespace.isStatic

    if (flags.isMutable)
      reportError("An exported property def cannot have the flag Mutable")
    if (flags.namespace.isPrivate)
      reportError("An exported property def cannot be private")

    if (!clazz.kind.isAnyNonNativeClass) {
      reportError(i"Exported property def can only appear in a class")
      return
    }

    checkExportedPropertyName(pName, clazz)

    val thisType =
      if (static) NoType
      else if (clazz.kind.isJSClass) AnyType
      else ClassType(clazz.name)

    getterBody.foreach { getterBody =>
      val getterBodyEnv = Env.fromSignature(thisType)
      typecheckExpect(getterBody, getterBodyEnv, AnyType)
    }

    setterArgAndBody.foreach { case (setterArg, setterBody) =>
      if (setterArg.ptpe != AnyType)
        reportError("Setter argument of exported property def has type "+
            i"${setterArg.ptpe}, but must be Any")

      val setterBodyEnv = Env.fromSignature(thisType)
      typecheckStat(setterBody, setterBodyEnv)
    }
  }

  private def checkExportedPropertyName(propName: Tree, clazz: CheckedClass)(
      implicit ctx: ErrorContext): Unit = {
    propName match {
      case StringLiteral(name) =>
        if (!clazz.kind.isJSClass && name.contains("__"))
          reportError("Exported method def name cannot contain __")

      case _ =>
        if (!clazz.kind.isJSClass)
          reportError("Only JS classes may contain members with computed names")
        typecheckExpect(propName, Env.empty, AnyType)
    }
  }

  private def checkTopLevelMethodExportDef(
      topLevelMethodExportDef: TopLevelMethodExportDef): Unit =  {

    val JSMethodDef(flags, pName, params, restParam, body) = topLevelMethodExportDef.methodDef
    implicit val ctx = ErrorContext(topLevelMethodExportDef.methodDef)

    if (flags.isMutable)
      reportError("Top level export method cannot have the flag Mutable")
    if (flags.namespace != MemberNamespace.PublicStatic)
      reportError("Top level export must be public and static")

    pName match {
      case StringLiteral(name) => // ok

      case _ =>
        reportError("Top level exports may not have computed names")
    }

    typecheckExpect(body, Env.empty, AnyType)
  }

  private def typecheckStat(tree: Tree, env: Env): Env = {
    implicit val ctx = ErrorContext(tree)

    tree match {
      case VarDef(ident, _, vtpe, mutable, rhs) =>
        typecheckExpect(rhs, env, vtpe)
        env

      case Skip() =>
        env

      case Assign(lhs, rhs) =>
        def checkNonStaticField(receiver: Tree, className: ClassName, name: FieldName): Unit = {
          receiver match {
            case This() if env.inConstructorOf == Some(className) =>
              // ok
            case _ =>
              if (lookupClass(className).lookupField(name).exists(!_.flags.isMutable))
                reportError(i"Assignment to immutable field $name.")
          }
        }

        lhs match {
          case Select(receiver, className, FieldIdent(name)) =>
            checkNonStaticField(receiver, className, name)
          case JSPrivateSelect(receiver, className, FieldIdent(name)) =>
            checkNonStaticField(receiver, className, name)
          case SelectStatic(className, FieldIdent(name)) =>
            val c = lookupClass(className)
            for {
              f <- c.lookupStaticField(name)
              if !f.flags.isMutable
            } {
              reportError(i"Assignment to immutable static field $name.")
            }
          case _:VarRef | _:ArraySelect | _:RecordSelect | _:JSSelect | _:JSSuperSelect | _:JSGlobalRef =>
        }
        val lhsTpe = typecheckExpr(lhs, env)
        typecheckExpect(rhs, env, lhsTpe)
        env

      case StoreModule(className, value) =>
        val clazz = lookupClass(className)
        if (!clazz.kind.hasModuleAccessor)
          reportError("StoreModule of non-module class $className")
        val expectedType =
          if (clazz.kind == ClassKind.JSModuleClass) AnyType
          else ClassType(className)
        typecheckExpect(value, env, expectedType)
        env

      case Block(stats) =>
        stats.foldLeft(env) { (prevEnv, stat) =>
          typecheckStat(stat, prevEnv)
        }
        env

      case Labeled(label, NoType, body) =>
        typecheckStat(body, env.withLabeledReturnType(label.name, AnyType))
        env

      case If(cond, thenp, elsep) =>
        typecheckExpect(cond, env, BooleanType)
        typecheckStat(thenp, env)
        typecheckStat(elsep, env)
        env

      case While(cond, body) =>
        typecheckExpect(cond, env, BooleanType)
        typecheckStat(body, env)
        env

      case DoWhile(body, cond) =>
        typecheckStat(body, env)
        typecheckExpect(cond, env, BooleanType)
        env

      case ForIn(obj, keyVar, _, body) =>
        typecheckExpr(obj, env)
        typecheckStat(body, env)
        env

      case TryCatch(block, errVar, _, handler) =>
        typecheckStat(block, env)
        typecheckStat(handler, env)
        env

      case TryFinally(block, finalizer) =>
        typecheckStat(block, env)
        typecheckStat(finalizer, env)
        env

      case Match(selector, cases, default) =>
        typecheckExpect(selector, env, IntType)
        // The alternatives are IntLiterals, no point typechecking them
        for ((_, body) <- cases)
          typecheckStat(body, env)
        typecheckStat(default, env)
        env

      case Debugger() =>
        env

      case JSDelete(qualifier, item) =>
        typecheckExpr(qualifier, env)
        typecheckExpr(item, env)
        env

      case _ =>
        typecheck(tree, env)
        env
    }
  }

  private def typecheckExpect(tree: Tree, env: Env, expectedType: Type)(
      implicit ctx: ErrorContext): Unit = {
    val tpe = typecheckExpr(tree, env)
    if (!isSubtype(tpe, expectedType))
      reportError(i"$expectedType expected but $tpe found "+
          i"for tree of type ${tree.getClass.getName}")
  }

  private def typecheckExpr(tree: Tree, env: Env): Type = {
    implicit val ctx = ErrorContext(tree)
    if (tree.tpe == NoType)
      reportError(i"Expression tree has type NoType")
    typecheck(tree, env)
  }

  private def typecheckExprOrSpread(tree: TreeOrJSSpread, env: Env): Unit = {
    tree match {
      case JSSpread(items) =>
        typecheckExpr(items, env)
      case tree: Tree =>
        typecheckExpr(tree, env)
    }
  }

  private def typecheck(tree: Tree, env: Env): Type = {
    implicit val ctx = ErrorContext(tree)

    def checkApplyGeneric(methodName: MethodName, methodFullName: String,
        args: List[Tree], tpe: Type, isStatic: Boolean): Unit = {
      val (methodParams, resultType) = inferMethodType(methodName, isStatic)
      if (args.size != methodParams.size)
        reportError(i"Arity mismatch: ${methodParams.size} expected but "+
            i"${args.size} found")
      for ((actual, formal) <- args zip methodParams) {
        typecheckExpect(actual, env, formal)
      }
      if (tpe != resultType)
        reportError(i"Call to $methodFullName of type $resultType "+
            i"typed as ${tree.tpe}")
    }

    tree match {
      // Control flow constructs

      case Block(statsAndExpr) =>
        val stats :+ expr = statsAndExpr
        val envAfterStats = stats.foldLeft(env) { (prevEnv, stat) =>
          typecheckStat(stat, prevEnv)
        }
        typecheckExpr(expr, envAfterStats)

      case Labeled(label, tpe, body) =>
        typecheckExpect(body, env.withLabeledReturnType(label.name, tpe), tpe)

      case Return(expr, label) =>
        env.returnTypes.get(label.name).fold[Unit] {
          reportError(i"Cannot return to label $label.")
          typecheckExpr(expr, env)
        } { returnType =>
          typecheckExpect(expr, env, returnType)
        }

      case If(cond, thenp, elsep) =>
        val tpe = tree.tpe
        typecheckExpect(cond, env, BooleanType)
        typecheckExpect(thenp, env, tpe)
        typecheckExpect(elsep, env, tpe)

      case While(BooleanLiteral(true), body) if tree.tpe == NothingType =>
        typecheckStat(body, env)

      case TryCatch(block, errVar, _, handler) =>
        val tpe = tree.tpe
        typecheckExpect(block, env, tpe)
        typecheckExpect(handler, env, tpe)

      case TryFinally(block, finalizer) =>
        val tpe = tree.tpe
        typecheckExpect(block, env, tpe)
        typecheckStat(finalizer, env)

      case Throw(expr) =>
        typecheckExpr(expr, env)

      case Match(selector, cases, default) =>
        val tpe = tree.tpe
        typecheckExpect(selector, env, IntType)
        // The alternatives are IntLiterals, no point typechecking them
        for ((_, body) <- cases)
          typecheckExpect(body, env, tpe)
        typecheckExpect(default, env, tpe)

      // Scala expressions

      case New(className, ctor, args) =>
        val clazz = lookupClass(className)
        if (clazz.kind != ClassKind.Class)
          reportError(i"new $className which is not a class")
        checkApplyGeneric(ctor.name, i"$className.$ctor", args, NoType,
            isStatic = false)

      case LoadModule(className) =>
        val clazz = lookupClass(className)
        if (clazz.kind != ClassKind.ModuleClass)
          reportError("LoadModule of non-module class $className")

      case Select(qualifier, className, FieldIdent(item)) =>
        val c = lookupClass(className)
        val kind = c.kind
        if (!kind.isClass) {
          reportError(i"Cannot select $item of non-class $className")
          typecheckExpr(qualifier, env)
        } else {
          typecheckExpect(qualifier, env, ClassType(className))

          /* Actually checking the field is done only if the class has
           * instances (including instances of subclasses).
           *
           * This is necessary because the BaseLinker can completely get rid
           * of all the fields of a class that has no instance. Obviously in
           * such cases, the only value that `qualifier` can assume is
           * `null`, and the `Select` will fail with an NPE. But the IR is
           * still valid per se.
           *
           * See #3060.
           */
          if (c.hasInstances) {
            c.lookupField(item).fold[Unit] {
              reportError(i"Class $className does not have a field $item")
            } { fieldDef =>
              if (fieldDef.tpe != tree.tpe)
                reportError(i"Select $className.$item of type "+
                    i"${fieldDef.tpe} typed as ${tree.tpe}")
            }
          }
        }

      case SelectStatic(className, FieldIdent(item)) =>
        val checkedClass = lookupClass(className)
        if (checkedClass.kind.isJSType) {
          reportError(i"Cannot select static $item of JS type $className")
        } else {
          checkedClass.lookupStaticField(item).fold[Unit] {
            reportError(i"Class $className does not have a static field $item")
          } { fieldDef =>
            if (fieldDef.tpe != tree.tpe)
              reportError(i"SelectStatic $className.$item of type "+
                  i"${fieldDef.tpe} typed as ${tree.tpe}")
          }
        }

      case SelectJSNativeMember(className, MethodIdent(member)) =>
        val checkedClass = lookupClass(className)
        if (!checkedClass.hasJSNativeMember(member))
          reportError(i"Class $className does not have JS native member $member")

      case Apply(flags, receiver, MethodIdent(method), args) =>
        if (flags.isPrivate)
          reportError("Illegal flag for Apply: Private")
        val receiverType = typecheckExpr(receiver, env)
        val fullCheck = receiverType match {
          case ClassType(className) =>
            /* For class types, we only perform full checks if the class has
             * instances. This is necessary because the BaseLinker can
             * completely get rid of all the method *definitions* for the call
             * method. In that case, the classes references in the *signature*
             * of the method might not have been made reachable, and hence
             * inferring the type signature might fail. Obviously in such cases,
             * the only value that `receiver` can assume is `null`, and the
             * `Apply` will fail with an NPE, so the types of the arguments are
             * irreleant.
             */
            lookupClass(className).hasInstances
          case NullType | NothingType =>
            // By a similar argument, we must not perform full checks here
            false
          case _ =>
            true
        }
        if (fullCheck) {
          checkApplyGeneric(method, i"$receiverType.$method", args, tree.tpe,
              isStatic = false)
        } else {
          for (arg <- args)
            typecheckExpr(arg, env)
        }

      case ApplyStatically(_, receiver, className, MethodIdent(method), args) =>
        typecheckExpect(receiver, env, ClassType(className))
        checkApplyGeneric(method, i"$className.$method", args, tree.tpe,
            isStatic = false)

      case ApplyStatic(_, className, MethodIdent(method), args) =>
        val clazz = lookupClass(className)
        checkApplyGeneric(method, i"$className.$method", args, tree.tpe,
            isStatic = true)

      case ApplyDynamicImport(_, className, MethodIdent(method), args) =>
        val clazz = lookupClass(className)
        val methodFullName = i"$className.$method"

        checkApplyGeneric(method, methodFullName, args, AnyType, isStatic = true)

        val resultType = method.resultTypeRef
        if (resultType != ClassRef(ObjectClass)) {
          reportError(i"illegal dynamic import call to $methodFullName with " +
              i"non-object result type: $resultType")
        }

      case UnaryOp(op, lhs) =>
        import UnaryOp._
        val expectedArgType = (op: @switch) match {
          case Boolean_! =>
            BooleanType
          case CharToInt =>
            CharType
          case ByteToInt =>
            ByteType
          case ShortToInt =>
            ShortType
          case IntToLong | IntToDouble | IntToChar | IntToByte | IntToShort =>
            IntType
          case LongToInt | LongToDouble | LongToFloat =>
            LongType
          case FloatToDouble =>
            FloatType
          case DoubleToInt | DoubleToFloat | DoubleToLong =>
            DoubleType
        }
        typecheckExpect(lhs, env, expectedArgType)

      case BinaryOp(op, lhs, rhs) =>
        import BinaryOp._
        val expectedLhsType = (op: @switch) match {
          case === | !== | String_+ =>
            AnyType
          case Boolean_== | Boolean_!= | Boolean_| | Boolean_& =>
            BooleanType
          case Int_+ | Int_- | Int_* | Int_/ | Int_% |
              Int_| | Int_& | Int_^ | Int_<< | Int_>>> | Int_>> |
              Int_== | Int_!= | Int_< | Int_<= | Int_> | Int_>= =>
            IntType
          case Long_+ | Long_- | Long_* | Long_/ | Long_% |
              Long_| | Long_& | Long_^ | Long_<< | Long_>>> | Long_>> |
              Long_== | Long_!= | Long_< | Long_<= | Long_> | Long_>= =>
            LongType
          case Float_+ | Float_- | Float_* | Float_/ | Float_% =>
            FloatType
          case Double_+ | Double_- | Double_* | Double_/ | Double_% |
              Double_== | Double_!= |
              Double_< | Double_<= | Double_> | Double_>= =>
            DoubleType
        }
        val expectedRhsType = (op: @switch) match {
          case Long_<< | Long_>>> | Long_>> => IntType
          case _                            => expectedLhsType
        }
        typecheckExpect(lhs, env, expectedLhsType)
        typecheckExpect(rhs, env, expectedRhsType)

      case NewArray(typeRef, lengths) =>
        for (length <- lengths)
          typecheckExpect(length, env, IntType)

      case ArrayValue(typeRef, elems) =>
        val elemType = arrayElemType(typeRef)
        for (elem <- elems)
          typecheckExpect(elem, env, elemType)

      case ArrayLength(array) =>
        val arrayType = typecheckExpr(array, env)
        if (!arrayType.isInstanceOf[ArrayType])
          reportError(i"Array type expected but $arrayType found")

      case ArraySelect(array, index) =>
        typecheckExpect(index, env, IntType)
        typecheckExpr(array, env) match {
          case arrayType: ArrayType =>
            if (tree.tpe != arrayElemType(arrayType))
              reportError(i"Array select of array type $arrayType typed as ${tree.tpe}")
          case arrayType =>
            reportError(i"Array type expected but $arrayType found")
        }

      case IsInstanceOf(expr, testType) =>
        typecheckExpr(expr, env)
        checkIsAsInstanceTargetType(testType)

      case AsInstanceOf(expr, tpe) =>
        typecheckExpr(expr, env)
        checkIsAsInstanceTargetType(tpe)

      case GetClass(expr) =>
        typecheckExpr(expr, env)

      case Clone(expr) =>
        typecheckExpect(expr, env, ClassType(CloneableClass))

      case IdentityHashCode(expr) =>
        typecheckExpr(expr, env)

      // JavaScript expressions

      case JSNew(ctor, args) =>
        typecheckExpr(ctor, env)
        for (arg <- args)
          typecheckExprOrSpread(arg, env)

      case JSPrivateSelect(qualifier, className, field) =>
        typecheckExpr(qualifier, env)
        val checkedClass = lookupClass(className)
        if (!checkedClass.kind.isJSClass && checkedClass.kind != ClassKind.AbstractJSType) {
          reportError(i"Cannot select JS private field $field of non-JS class $className")
        } else {
          if (checkedClass.lookupField(field.name).isEmpty)
            reportError(i"JS class $className does not have a field $field")
          /* The declared type of the field is irrelevant here. It is only
           * relevant for its initialization value. The type of the selection
           * is always `any`.
           */
        }

      case JSSelect(qualifier, item) =>
        typecheckExpr(qualifier, env)
        typecheckExpr(item, env)

      case JSFunctionApply(fun, args) =>
        typecheckExpr(fun, env)
        for (arg <- args)
          typecheckExprOrSpread(arg, env)

      case JSMethodApply(receiver, method, args) =>
        typecheckExpr(receiver, env)
        typecheckExpr(method, env)
        for (arg <- args)
          typecheckExprOrSpread(arg, env)

      case JSSuperSelect(superClass, qualifier, item) =>
        typecheckExpr(superClass, env)
        typecheckExpr(qualifier, env)
        typecheckExpr(item, env)

      case JSSuperMethodCall(superClass, receiver, method, args) =>
        typecheckExpr(superClass, env)
        typecheckExpr(receiver, env)
        typecheckExpr(method, env)
        for (arg <- args)
          typecheckExprOrSpread(arg, env)

      case JSImportCall(arg) =>
        typecheckExpr(arg, env)

      case LoadJSConstructor(className) =>
        val clazz = lookupClass(className)
        val valid = clazz.kind match {
          case ClassKind.JSClass       => true
          case ClassKind.NativeJSClass => true
          case _                       => false
        }
        if (!valid)
          reportError(i"JS class type expected but $className found")
        else if (clazz.jsClassCaptures.nonEmpty)
          reportError(i"Cannot load JS constructor of non-top-level class $className")
        else if (clazz.kind == ClassKind.NativeJSClass && clazz.jsNativeLoadSpec.isEmpty)
          reportError(i"Cannot load JS constructor of native JS class $className without native load spec")

      case LoadJSModule(className) =>
        val clazz = lookupClass(className)
        val valid = clazz.kind match {
          case ClassKind.JSModuleClass       => true
          case ClassKind.NativeJSModuleClass => true
          case _                             => false
        }
        if (!valid)
          reportError(i"JS module class type expected but $className found")
        else if (clazz.kind == ClassKind.NativeJSModuleClass && clazz.jsNativeLoadSpec.isEmpty)
          reportError(i"Cannot load JS module of native JS module class $className without native load spec")

      case JSUnaryOp(op, lhs) =>
        typecheckExpr(lhs, env)

      case JSBinaryOp(op, lhs, rhs) =>
        typecheckExpr(lhs, env)
        typecheckExpr(rhs, env)

      case JSArrayConstr(items) =>
        for (item <- items)
          typecheckExprOrSpread(item, env)

      case JSObjectConstr(fields) =>
        for ((key, value) <- fields) {
          typecheckExpr(key, env)
          typecheckExpr(value, env)
        }

      case JSGlobalRef(_) =>

      case JSTypeOfGlobalRef(_) =>

      case JSLinkingInfo() =>

      // Literals

      case _: Literal =>

      // Atomic expressions

      case _: VarRef =>

      case This() =>
        if (!isSubtype(env.thisTpe, tree.tpe))
          reportError(i"this of type ${env.thisTpe} typed as ${tree.tpe}")

      case Closure(arrow, captureParams, params, restParam, body, captureValues) =>
        // Check compliance of captureValues wrt. captureParams in the current env
        for ((ParamDef(_, _, ctpe, _), value) <- captureParams zip captureValues) {
          typecheckExpect(value, env, ctpe)
        }

        // Then check the closure params and body in its own env
        val thisType = if (arrow) NoType else AnyType
        val bodyEnv = Env.fromSignature(thisType)
        typecheckExpect(body, bodyEnv, AnyType)

      case CreateJSClass(className, captureValues) =>
        val clazz = lookupClass(className)
        clazz.jsClassCaptures.fold {
          reportError(i"Invalid CreateJSClass of top-level class $className")
        } { captureParams =>
          if (captureParams.size != captureValues.size) {
            reportError("Mismatched size for class captures: " +
                i"${captureParams.size} params vs ${captureValues.size} values")
          }

          for ((ParamDef(_, _, ctpe, _), value) <- captureParams.zip(captureValues))
            typecheckExpect(value, env, ctpe)
        }

      case _ =>
        reportError(i"Invalid expression tree")
    }

    tree.tpe
  }

  private def checkIsAsInstanceTargetType(tpe: Type)(
      implicit ctx: ErrorContext): Unit = {
    tpe match {
      case ClassType(className) =>
        val kind = lookupClass(className).kind
        if (kind.isJSType) {
          reportError(
              i"JS type $className is not a valid target type for " +
              "Is/AsInstanceOf")
        }

      case _ =>
        // ok
    }
  }

  private def inferMethodType(methodName: MethodName, isStatic: Boolean)(
      implicit ctx: ErrorContext): (List[Type], Type) = {

    val paramTypes = methodName.paramTypeRefs.map(typeRefToType)
    val resultType = typeRefToType(methodName.resultTypeRef)
    (paramTypes, resultType)
  }

  private def typeRefToType(typeRef: TypeRef)(
      implicit ctx: ErrorContext): Type = {
    typeRef match {
      case PrimRef(tpe)               => tpe
      case ClassRef(className)        => classNameToType(className)
      case arrayTypeRef: ArrayTypeRef => ArrayType(arrayTypeRef)
    }
  }

  private def classNameToType(className: ClassName)(
      implicit ctx: ErrorContext): Type = {
    if (className == ObjectClass) {
      AnyType
    } else {
      val kind = lookupClass(className).kind
      if (kind.isJSType) AnyType
      else ClassType(className)
    }
  }

  private def arrayElemType(arrayType: ArrayType)(
      implicit ctx: ErrorContext): Type = {
    arrayElemType(arrayType.arrayTypeRef)
  }

  private def arrayElemType(arrayTypeRef: ArrayTypeRef)(
      implicit ctx: ErrorContext): Type = {
    val ArrayTypeRef(base, dimensions) = arrayTypeRef
    if (dimensions == 1)
      typeRefToType(base)
    else
      ArrayType(ArrayTypeRef(base, dimensions - 1))
  }

  private def lookupClass(className: ClassName)(
      implicit ctx: ErrorContext): CheckedClass = {
    classes.getOrElseUpdate(className, {
      reportError(i"Cannot find class $className")
      new CheckedClass(className, ClassKind.Class, None, Some(ObjectClass),
          Set(ObjectClass), hasInstances = true, None, Nil, Set.empty)
    })
  }

  private def lookupClass(classType: ClassType)(
      implicit ctx: ErrorContext): CheckedClass = {
    lookupClass(classType.className)
  }

  private def lookupClass(classRef: ClassRef)(
      implicit ctx: ErrorContext): CheckedClass = {
    lookupClass(classRef.className)
  }

  private def isSubclass(lhs: ClassName, rhs: ClassName)(
      implicit ctx: ErrorContext): Boolean = {
    lookupClass(lhs).ancestors.contains(rhs)
  }

  private def isSubtype(lhs: Type, rhs: Type)(
      implicit ctx: ErrorContext): Boolean = {
    Types.isSubtype(lhs, rhs)(isSubclass)
  }

  private class Env(
      /** Type of `this`. Can be NoType. */
      val thisTpe: Type,
      /** Return types by label. */
      val returnTypes: Map[LabelName, Type],
      /** Whether we're in a constructor of the class */
      val inConstructorOf: Option[ClassName]
  ) {
    import Env._

    def withThis(thisTpe: Type): Env =
      new Env(thisTpe, this.returnTypes, this.inConstructorOf)

    def withLabeledReturnType(label: LabelName, returnType: Type): Env =
      new Env(this.thisTpe, returnTypes + (label -> returnType), this.inConstructorOf)
  }

  private object Env {
    val empty: Env = new Env(NoType, Map.empty, None)

    def fromSignature(thisType: Type, inConstructorOf: Option[ClassName] = None): Env = {
      new Env(thisType, Map.empty, inConstructorOf)
    }
  }

  private class CheckedClass(
      val name: ClassName,
      val kind: ClassKind,
      val jsClassCaptures: Option[List[ParamDef]],
      val superClassName: Option[ClassName],
      val ancestors: Set[ClassName],
      val hasInstances: Boolean,
      val jsNativeLoadSpec: Option[JSNativeLoadSpec],
      _fields: List[CheckedField],
      val jsNativeMembers: Set[MethodName])(
      implicit ctx: ErrorContext) {

    val fields = _fields.filter(!_.flags.namespace.isStatic).map(f => f.name -> f).toMap
    val staticFields = _fields.filter(_.flags.namespace.isStatic).map(f => f.name -> f).toMap

    lazy val superClass = superClassName.map(classes)

    def this(classDef: LinkedClass)(implicit ctx: ErrorContext) = {
      this(classDef.name.name, classDef.kind,
          classDef.jsClassCaptures,
          classDef.superClass.map(_.name),
          classDef.ancestors.toSet,
          classDef.hasInstances,
          classDef.jsNativeLoadSpec,
          CheckedClass.checkedFieldsOf(classDef),
          classDef.jsNativeMembers.map(_.name.name).toSet)
    }

    def lookupField(name: FieldName): Option[CheckedField] =
      fields.get(name)

    def lookupStaticField(name: FieldName): Option[CheckedField] =
      staticFields.get(name)

    def hasJSNativeMember(name: MethodName): Boolean =
      jsNativeMembers.contains(name)
  }

  private object CheckedClass {
    private def checkedFieldsOf(classDef: LinkedClass): List[CheckedField] = {
      classDef.fields.collect {
        case FieldDef(flags, FieldIdent(name), _, tpe) =>
          new CheckedField(flags, name, tpe)
      }
    }
  }

  private class CheckedField(val flags: MemberFlags, val name: FieldName,
      val tpe: Type)
}

object IRChecker {
  /** Checks that the IR in a [[frontend.LinkingUnit LinkingUnit]] is correct.
   *
   *  @return Count of IR checking errors (0 in case of success)
   */
  def check(unit: LinkingUnit, logger: Logger): Int = {
    val reporter = new ErrorReporter(logger)
    new IRChecker(unit, reporter).check()
    reporter.errorCount
  }
}
