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

package org.scalajs.linker.backend.closure

import scala.annotation.switch

import org.scalajs.ir
import ir.Position
import ir.Position.NoPosition

import org.scalajs.linker.backend.javascript.Trees._
import org.scalajs.linker.backend.javascript.SourceFileUtil

import com.google.javascript.rhino._
import com.google.javascript.rhino.StaticSourceFile.SourceKind
import com.google.javascript.jscomp.SourceFile
import com.google.javascript.jscomp.parsing.parser.FeatureSet

import scala.annotation.tailrec

import java.net.URI

private[closure] object ClosureAstTransformer {
  def transformScript(tree: Tree, featureSet: FeatureSet, relativizeBaseURI: Option[URI]): Node = {
    val transformer = new ClosureAstTransformer(featureSet, relativizeBaseURI)
    transformer.transformScript(tree)
  }
}

private class ClosureAstTransformer(featureSet: FeatureSet, relativizeBaseURI: Option[URI]) {
  private val dummySourceName = new java.net.URI("virtualfile:scala.js-ir")

  def transformScript(tree: Tree): Node = {
    /* Top-level `js.Block`s must be explicitly flattened here.
     * Our `js.Block`s do not have the same semantics as GCC's `BLOCK`s: GCC's
     * impose strict scoping for `let`s, `const`s and `class`es, while ours are
     * only a means of putting together several statements in one `js.Tree`
     * (in fact, they automatically flatten themselves out upon construction).
     */
    val script = setNodePosition(new Node(Token.SCRIPT), NoPosition)

    tree match {
      case Block(stats) =>
        transformBlockStats(stats)(NoPosition).foreach(script.addChildToBack(_))

      case Skip() =>

      case tree =>
        script.addChildToBack(transformStat(tree)(NoPosition))
    }

    script.putProp(Node.FEATURE_SET, featureSet)

    script
  }

  def transformStat(tree: Tree)(implicit parentPos: Position): Node =
    innerTransformStat(tree, tree.pos.orElse(parentPos))

  private def innerTransformStat(tree: Tree, pos_in: Position): Node = {
    implicit val pos = pos_in

    wrapTransform(tree) {
      case VarDef(ident, optRhs) =>
        val node = transformName(ident)
        optRhs.foreach(rhs => node.addChildToFront(transformExpr(rhs)))
        new Node(Token.VAR, node)
      case Let(ident, mutable, optRhs) =>
        val node = transformName(ident)
        optRhs.foreach(rhs => node.addChildToFront(transformExpr(rhs)))
        /* #4098 The following line should be
         *   new Node(if (mutable) Token.LET else Token.CONST, node)
         * however, due to an unknown bug in how we build GCC trees or inside
         * GCC itself, using `let`s and `const`s can result in a crash deep
         * inside GCC in some obscure cases.
         * As a workaround, we always emit `var`s instead. This has no visible
         * semantic change because the Emitter never relies on the specific
         * semantics of `let`s and `const`s.
         * TODO We should properly fix this at the root (filed as #4109).
         */
        new Node(Token.VAR, node)
      case Skip() =>
        new Node(Token.EMPTY)
      case Block(stats) =>
        transformBlock(stats, pos)
      case Labeled(label, body) =>
        new Node(Token.LABEL, transformLabel(label), transformBlock(body))
      case Return(expr) =>
        new Node(Token.RETURN, transformExpr(expr))
      case If(cond, thenp, Skip()) =>
        new Node(Token.IF, transformExpr(cond), transformBlock(thenp))
      case If(cond, thenp, elsep) =>
        new Node(Token.IF, transformExpr(cond), transformBlock(thenp), transformBlock(elsep))
      case While(cond, body, None) =>
        new Node(Token.WHILE, transformExpr(cond), transformBlock(body))
      case While(cond, body, Some(label)) =>
        val whileNode =
          new Node(Token.WHILE, transformExpr(cond), transformBlock(body))
        new Node(Token.LABEL, transformLabel(label), setNodePosition(whileNode, pos))
      case DoWhile(body, cond, None) =>
        new Node(Token.DO, transformBlock(body), transformExpr(cond))
      case DoWhile(body, cond, Some(label)) =>
        val doNode =
          new Node(Token.DO, transformBlock(body), transformExpr(cond))
        new Node(Token.LABEL, transformLabel(label), setNodePosition(doNode, pos))
      case ForIn(lhs, obj, body) =>
        new Node(Token.FOR_IN, transformStat(lhs), transformExpr(obj), transformBlock(body))
      case For(init, guard, update, body) =>
        // There is no constructor for Node with 4 children
        val forNode =
          new Node(Token.FOR, transformStat(init), transformExpr(guard), transformStat(update))
        forNode.addChildToBack(transformBlock(body))
        forNode
      case TryFinally(TryCatch(block, errVar, handler), finalizer) =>
        val catchPos = handler.pos.orElse(pos)
        val catchNode =
          new Node(Token.CATCH, transformName(errVar), transformBlock(handler))
        val blockNode =
          new Node(Token.BLOCK, setNodePosition(catchNode, catchPos))
        new Node(Token.TRY, transformBlock(block), setNodePosition(blockNode, catchPos),
            transformBlock(finalizer))
      case TryCatch(block, errVar, handler) =>
        val catchPos = handler.pos.orElse(pos)
        val catchNode =
          new Node(Token.CATCH, transformName(errVar), transformBlock(handler))
        val blockNode =
          new Node(Token.BLOCK, setNodePosition(catchNode, catchPos))
        new Node(Token.TRY, transformBlock(block), setNodePosition(blockNode, catchPos))
      case TryFinally(block, finalizer) =>
        val blockNode = setNodePosition(new Node(Token.BLOCK), pos)
        new Node(Token.TRY, transformBlock(block), blockNode, transformBlock(finalizer))
      case Throw(expr) =>
        new Node(Token.THROW, transformExpr(expr))
      case Break(None) =>
        new Node(Token.BREAK)
      case Break(Some(label)) =>
        new Node(Token.BREAK, transformLabel(label))
      case Continue(None) =>
        new Node(Token.CONTINUE)
      case Continue(Some(label)) =>
        new Node(Token.CONTINUE, transformLabel(label))

      case Switch(selector, cases, default) =>
        val switchNode = new Node(Token.SWITCH, transformExpr(selector))

        def transformBody(body: Tree): Node = {
          /* Transform the body of a switch case or default, then wrap the
           * result in a synthetic block. The synthetic block is important for
           * switches, but at the same time we must not flatten out an actual
           * Block(), lest we conflate the scopes for local declarations.
           */
          val block = new Node(Token.BLOCK)
          block.addChildToBack(transformStat(body))
          block.setIsSyntheticBlock(true)
          setNodePosition(block, body.pos.orElse(pos))
          block
        }

        for ((expr, body) <- cases) {
          val bodyNode = transformBody(body)
          val caseNode = new Node(Token.CASE, transformExpr(expr), bodyNode)
          switchNode.addChildToBack(setNodePosition(caseNode, expr.pos.orElse(pos)))
        }

        val bodyNode = transformBody(default)
        val caseNode = new Node(Token.DEFAULT_CASE, bodyNode)
        switchNode.addChildToBack(setNodePosition(caseNode, default.pos.orElse(pos)))

        switchNode

      case Debugger() =>
        new Node(Token.DEBUGGER)

      case FunctionDef(name, args, body) =>
        val node = transformName(name)
        val rhs = genFunction(name.name, args, body)
        node.addChildToFront(rhs)
        new Node(Token.VAR, node)

      case classDef: ClassDef =>
        transformClassDef(classDef)

      case _ =>
        // We just assume it is an expression
        new Node(Token.EXPR_RESULT, transformExpr(tree))
    }
  }

  private def transformClassDef(classDef: ClassDef)(implicit pos: Position): Node = {
    val ClassDef(className, parentClass, members) = classDef

    val membersBlock = new Node(Token.CLASS_MEMBERS)
    for (member <- members)
      membersBlock.addChildToBack(transformClassMember(member))
    new Node(Token.CLASS, className.fold(new Node(Token.EMPTY))(transformName(_)),
        parentClass.fold(new Node(Token.EMPTY))(transformExpr(_)), membersBlock)
  }

  private def transformClassMember(member: Tree): Node = {
    implicit val pos = member.pos

    def newFixedPropNode(token: Token, static: Boolean, name: Ident, function: Node): Node = {
      val node = Node.newString(token, name.name)
      node.addChildToBack(function)
      node.setStaticMember(static)
      node
    }

    /* This method should take a `prop: Node.Prop` parameter to factor out
     * the `node.putBooleanProp()` that we find the three cases below. However,
     * that is not possible because `Node.Prop` is private in `Node`. Go figure
     * why Java allows to export as `public` the aliases
     * `Node.COMPUTED_PROP_METHOD` et al. with a type that is not public ...
     */
    def newComputedPropNode(static: Boolean, nameExpr: Tree, function: Node): Node = {
      val node = new Node(Token.COMPUTED_PROP, transformExpr(nameExpr), function)
      node.setStaticMember(static)
      node
    }

    wrapTransform(member) {
      case MethodDef(static, name, args, body) =>
        val function = genFunction("", args, body)
        name match {
          case ComputedName(nameExpr) =>
            val node = newComputedPropNode(static, nameExpr, function)
            node.putBooleanProp(Node.COMPUTED_PROP_METHOD, true)
            node
          case nameExpr: StringLiteral =>
            /* I think this case should not be necessary, and that
             * newFixedPropNode below should work for StringLiterals as well
             * as Idents (with a QuotedString in GCC's AST). However, if we do
             * that, GCC systematically ignores the definition of the method.
             * To be fair, there is a comment on StringNode.setIsQuotedString()
             * that reads
             *
             * > This should only be called for STRING nodes created in object
             * > lits.
             *
             * which does suggest that COMPUTED_PROP must be used instead.
             * This analysis is also supported by the fact that string-literal
             * method declarations in source are systematically compiled as
             * computed-named methods by GCC when used outside Scala.js.
             */
            val node = newComputedPropNode(static, nameExpr, function)
            node.putBooleanProp(Node.COMPUTED_PROP_METHOD, true)
            node
          case name: Ident =>
            newFixedPropNode(Token.MEMBER_FUNCTION_DEF, static, name, function)
        }

      case GetterDef(static, name, body) =>
        val function = genFunction("", Nil, body)
        name match {
          case ComputedName(nameExpr) =>
            val node = newComputedPropNode(static, nameExpr, function)
            node.putBooleanProp(Node.COMPUTED_PROP_GETTER, true)
            node
          case nameExpr: StringLiteral =>
            // See comment above in case MethodDef
            val node = newComputedPropNode(static, nameExpr, function)
            node.putBooleanProp(Node.COMPUTED_PROP_GETTER, true)
            node
          case name: Ident =>
            newFixedPropNode(Token.GETTER_DEF, static, name, function)
        }

      case SetterDef(static, name, param, body) =>
        val function = genFunction("", param :: Nil, body)
        name match {
          case ComputedName(nameExpr) =>
            val node = newComputedPropNode(static, nameExpr, function)
            node.putBooleanProp(Node.COMPUTED_PROP_SETTER, true)
            node
          case nameExpr: StringLiteral =>
            // See comment above in case MethodDef
            val node = newComputedPropNode(static, nameExpr, function)
            node.putBooleanProp(Node.COMPUTED_PROP_SETTER, true)
            node
          case name: Ident =>
            newFixedPropNode(Token.SETTER_DEF, static, name, function)
        }

      case _ =>
        throw new AssertionError(
            s"Unexpected class member tree of class ${member.getClass.getName}")
    }
  }

  def transformExpr(tree: Tree)(implicit parentPos: Position): Node =
    innerTransformExpr(tree, tree.pos.orElse(parentPos))

  private def innerTransformExpr(tree: Tree, pos_in: Position): Node = {
    implicit val pos = pos_in

    wrapTransform(tree) {
      case Block(exprs) =>
        exprs.map(transformExpr).reduceRight { (expr1, expr2) =>
          setNodePosition(new Node(Token.COMMA, expr1, expr2), pos)
        }
      case If(cond, thenp, elsep) =>
        new Node(Token.HOOK, transformExpr(cond), transformExpr(thenp), transformExpr(elsep))
      case Assign(lhs, rhs) =>
        new Node(Token.ASSIGN, transformExpr(lhs), transformExpr(rhs))
      case New(ctor, args) =>
        val node = new Node(Token.NEW, transformExpr(ctor))
        args.foreach(arg => node.addChildToBack(transformExpr(arg)))
        node
      case DotSelect(qualifier, item) =>
        new Node(Token.GETPROP, transformExpr(qualifier), transformString(item))
      case BracketSelect(qualifier, item) =>
        new Node(Token.GETELEM, transformExpr(qualifier), transformExpr(item))

      case Apply(fun, args) =>
        val node = new Node(Token.CALL, transformExpr(fun))
        args.foreach(arg => node.addChildToBack(transformExpr(arg)))

        // Closure needs to know (from the parser), if the call has a bound
        // `this` or not. Since JSDesugar inserts protects calls if necessary,
        // it is sufficient to check if we have a select as target
        if (!fun.isInstanceOf[DotSelect] &&
            !fun.isInstanceOf[BracketSelect])
          node.putBooleanProp(Node.FREE_CALL, true)

        node

      case ImportCall(arg) =>
        new Node(Token.DYNAMIC_IMPORT, transformExpr(arg))
      case Delete(prop) =>
        new Node(Token.DELPROP, transformExpr(prop))
      case UnaryOp(op, lhs) =>
        mkUnaryOp(op, transformExpr(lhs))
      case IncDec(prefix, inc, arg) =>
        val token = if (inc) Token.INC else Token.DEC
        val node = new Node(token, transformExpr(arg))
        if (!prefix)
          node.putBooleanProp(Node.INCRDECR_PROP, true)
        node
      case BinaryOp(op, lhs, rhs) =>
        mkBinaryOp(op, transformExpr(lhs), transformExpr(rhs))
      case ArrayConstr(items) =>
        val node = new Node(Token.ARRAYLIT)
        items.foreach(i => node.addChildToBack(transformExpr(i)))
        node
      case ObjectConstr(fields) =>
        val node = new Node(Token.OBJECTLIT)
        for ((name, value) <- fields)
          node.addChildToBack(transformObjectLitField(name, value))
        node

      case Undefined() =>
        new Node(Token.VOID, setNodePosition(Node.newNumber(0.0), pos))
      case Null() =>
        new Node(Token.NULL)
      case BooleanLiteral(value) =>
        if (value) new Node(Token.TRUE) else new Node(Token.FALSE)
      case IntLiteral(value) =>
        Node.newNumber(value)
      case DoubleLiteral(value) =>
        Node.newNumber(value)
      case StringLiteral(value) =>
        Node.newString(value)
      case VarRef(ident) =>
        transformName(ident)
      case This() =>
        new Node(Token.THIS)
      case Super() =>
        new Node(Token.SUPER)

      case Function(arrow, args, body) =>
        val node = genFunction("", args, body)
        node.setIsArrowFunction(arrow)
        node
      case FunctionDef(name, args, body) =>
        genFunction(name.name, args, body)

      case classDef: ClassDef =>
        transformClassDef(classDef)

      case Spread(items) =>
        new Node(Token.ITER_SPREAD, transformExpr(items))

      case _ =>
        throw new TransformException(s"Unknown tree of class ${tree.getClass()}")
    }
  }

  private def genFunction(name: String, args: List[ParamDef], body: Tree)(
      implicit pos: Position): Node = {
    val paramList = new Node(Token.PARAM_LIST)
    args.foreach(arg => paramList.addChildToBack(transformParam(arg)))

    val nameNode = setNodePosition(Node.newString(Token.NAME, name), pos)

    new Node(Token.FUNCTION, nameNode, paramList, transformBlock(body))
  }

  def transformParam(param: ParamDef)(implicit parentPos: Position): Node = {
    val pos = if (param.pos.isDefined) param.pos else parentPos
    val node = transformName(param.name)(pos)
    if (param.rest)
      setNodePosition(new Node(Token.ITER_REST, node), pos)
    else
      node
  }

  def transformName(ident: Ident)(implicit parentPos: Position): Node =
    setNodePosition(Node.newString(Token.NAME, ident.name), ident.pos.orElse(parentPos))

  def transformLabel(ident: Ident)(implicit parentPos: Position): Node =
    setNodePosition(Node.newString(Token.LABEL_NAME, ident.name), ident.pos.orElse(parentPos))

  def transformString(ident: Ident)(implicit parentPos: Position): Node =
    setNodePosition(Node.newString(ident.name), ident.pos.orElse(parentPos))

  def transformObjectLitField(name: PropertyName, value: Tree)(
      implicit parentPos: Position): Node = {

    val transformedValue = transformExpr(value)

    val node = name match {
      case Ident(name, _) =>
        Node.newString(Token.STRING_KEY, name)

      case StringLiteral(name) =>
        val node = Node.newString(Token.STRING_KEY, name)
        node.setQuotedString()
        node

      case ComputedName(nameExpr) =>
        new Node(Token.COMPUTED_PROP, transformExpr(nameExpr))
    }

    node.addChildToBack(transformExpr(value))
    setNodePosition(node, name.pos.orElse(parentPos))
  }

  def transformBlock(tree: Tree)(implicit parentPos: Position): Node = {
    val pos = if (tree.pos.isDefined) tree.pos else parentPos
    wrapTransform(tree) {
      case Block(stats) =>
        transformBlock(stats, pos)
      case tree =>
        transformBlock(List(tree), pos)
    }(pos)
  }

  def transformBlock(stats: List[Tree], blockPos: Position): Node = {
    val block = new Node(Token.BLOCK)
    for (node <- transformBlockStats(stats)(blockPos))
      block.addChildToBack(node)
    block
  }

  def transformBlockStats(stats: List[Tree])(implicit parentPos: Position): List[Node] = {

    @inline def ctorDoc() = {
      val b = new JSDocInfoBuilder(false)
      b.recordConstructor()
      b.build()
    }

    // The Rhino IR attaches DocComments to the following nodes (rather than
    // having individual nodes). We preprocess these here.
    @tailrec
    def loop(ts: List[Tree], nextIsCtor: Boolean, acc: List[Node]): List[Node] = ts match {
      case DocComment(text) :: tss =>
        loop(tss, nextIsCtor = text.startsWith("@constructor"), acc)

      case t :: tss =>
        val node = transformStat(t)
        if (nextIsCtor) {
          // The @constructor must be propagated through an ExprResult node
          val trg =
            if (node.isExprResult()) node.getChildAtIndex(0)
            else node
          trg.setJSDocInfo(ctorDoc())
        }
        loop(tss, nextIsCtor = false, node :: acc)

      case Nil =>
        acc.reverse
    }

    loop(stats, nextIsCtor = false, Nil)
  }

  @inline
  private def wrapTransform(tree: Tree)(body: Tree => Node)(implicit pos: Position): Node = {
    try {
      setNodePosition(body(tree), pos)
    } catch {
      case e: TransformException =>
        throw e // pass through
      case e: RuntimeException =>
        throw new TransformException(tree, e)
    }
  }

  private def setNodePosition(node: Node, pos: ir.Position): node.type = {
    if (pos != ir.Position.NoPosition) {
      attachSourceFile(node, pos.source)
      node.setLineno(pos.line + 1)
      node.setCharno(pos.column)
    } else {
      attachSourceFile(node, dummySourceName)
    }
    node
  }

  private def attachSourceFile(node: Node, source: URI): node.type = {
    val str = SourceFileUtil.webURI(relativizeBaseURI, source)
    val file = new SourceFile(str, SourceKind.STRONG)

    /* A lot of Closure code makes the assumption that the InputId is the
     * filename. We follow this assumption so we can use more of the already
     * provided classes that make this assumption.
     */
    node.setInputId(new InputId(file.getName()))
    node.setStaticSourceFile(file)

    node
  }

  // Helpers for IR
  @inline
  private def mkUnaryOp(op: UnaryOp.Code, lhs: Node): Node = {
    import ir.Trees.JSUnaryOp._
    val tok = (op: @switch) match {
      case !        => Token.NOT
      case ~        => Token.BITNOT
      case +        => Token.POS
      case -        => Token.NEG
      case `typeof` => Token.TYPEOF
    }

    new Node(tok, lhs)
  }

  @inline
  private def mkBinaryOp(op: BinaryOp.Code, lhs: Node, rhs: Node): Node = {
    import ir.Trees.JSBinaryOp._
    val tok = (op: @switch) match {
      case === => Token.SHEQ
      case !== => Token.SHNE

      case + => Token.ADD
      case - => Token.SUB
      case * => Token.MUL
      case / => Token.DIV
      case % => Token.MOD

      case |   => Token.BITOR
      case &   => Token.BITAND
      case ^   => Token.BITXOR
      case <<  => Token.LSH
      case >>  => Token.RSH
      case >>> => Token.URSH

      case <  => Token.LT
      case <= => Token.LE
      case >  => Token.GT
      case >= => Token.GE

      case || => Token.OR
      case && => Token.AND

      case `in`         => Token.IN
      case `instanceof` => Token.INSTANCEOF
    }

    new Node(tok, lhs, rhs)
  }

  // Exception wrapper in transforms

  class TransformException private (msg: String, e: Throwable) extends RuntimeException(msg, e) {

    def this(tree: Tree, e: Throwable) =
      this(TransformException.mkMsg(tree), e)

    def this(msg: String) = this(msg, null)
  }

  object TransformException {
    import ir.Printers._
    import java.io._

    private def mkMsg(tree: Tree): String = {
      "Exception while translating Scala.js JS tree to GCC IR at tree:\n" +
        tree.show
    }
  }

}
