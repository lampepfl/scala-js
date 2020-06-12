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

package org.scalajs.linker

import scala.concurrent._

import org.junit.Test
import org.junit.Assert._

import org.scalajs.ir.ClassKind
import org.scalajs.ir.EntryPointsInfo
import org.scalajs.ir.Names._
import org.scalajs.ir.Trees._
import org.scalajs.ir.Trees.MemberNamespace._
import org.scalajs.ir.Types._

import org.scalajs.logging._

import org.scalajs.junit.async._

import org.scalajs.linker.interface._
import org.scalajs.linker.standard._

import org.scalajs.linker.testutils._
import org.scalajs.linker.testutils.IRAssertions._
import org.scalajs.linker.testutils.TestIRBuilder._

class OptimizerTest {
  import scala.concurrent.ExecutionContext.Implicits.global

  import OptimizerTest._

  /** Generic code for the three methods below.
   *
   *  Check that `clone()` is never inlined when the result can be an array,
   *  in several scenarios.
   */
  private def testCloneOnArrayNotInlinedGeneric(
      customMemberDefs: List[MemberDef]): Future[Unit] = {

    val thisFoo = This()(ClassType("Foo"))
    val intArrayTypeRef = ArrayTypeRef(IntRef, 1)
    val intArrayType = ArrayType(intArrayTypeRef)
    val anArrayOfInts = ArrayValue(intArrayTypeRef, List(IntLiteral(1)))
    val newFoo = New("Foo", NoArgConstructorName, Nil)

    val reachCloneMethodName = m("reachClone", Nil, O)
    val anArrayMethodName = m("anArray", Nil, intArrayTypeRef)
    val anObjectMethodName = m("anObject", Nil, O)

    def callCloneOn(receiver: Tree): Tree =
      Apply(EAF, receiver, cloneMethodName, Nil)(AnyType)

    val fooMemberDefs = List(
        trivialCtor("Foo"),

        // @noinline def witness(): AnyRef = throw null
        MethodDef(EMF, witnessMethodName, NON, Nil, AnyType, Some {
          Throw(Null())
        })(EOH.withNoinline(true), None),

        // @noinline def reachClone(): Object = clone()
        MethodDef(EMF, reachCloneMethodName, NON, Nil, AnyType, Some {
          Apply(EAF, thisFoo, cloneMethodName, Nil)(AnyType)
        })(EOH.withNoinline(true), None),

        // @noinline def anArray(): Array[Int] = Array(1)
        MethodDef(EMF, anArrayMethodName, NON, Nil, intArrayType, Some {
          anArrayOfInts
        })(EOH.withNoinline(true), None),

        // @noinline def anObject(): AnyRef = Array(1)
        MethodDef(EMF, anObjectMethodName, NON, Nil, AnyType, Some {
          anArrayOfInts
        })(EOH.withNoinline(true), None)
    ) ::: customMemberDefs

    val classDefs = Seq(
        classDef("Foo",
            superClass = Some(ObjectClass),
            interfaces = List("java.lang.Cloneable"),
            memberDefs = fooMemberDefs
        ),
        mainTestClassDef(Block(
            // new Foo().reachClone() -- make Foo.clone() reachable for sure
            Apply(EAF, newFoo, reachCloneMethodName, Nil)(AnyType),
            // Array(1).clone() -- test with an exact static type of I[]
            callCloneOn(anArrayOfInts),
            // new Foo().anArray().clone() -- test with a static type of I[]
            callCloneOn(Apply(EAF, newFoo, anArrayMethodName, Nil)(intArrayType)),
            // new Foo().anObject().clone() -- test with a static type of Object
            callCloneOn(Apply(EAF, newFoo, anObjectMethodName, Nil)(AnyType))
        ))
    )

    for (linkingUnit <- linkToLinkingUnit(classDefs, MainTestModuleInitializers)) yield {
      val linkedClass = linkingUnit.classDefs.find(_.className == MainTestClassName).get
      val ObjectCloneClass = ClassName("java.lang.ObjectClone$")
      linkedClass.hasNot("any call to Foo.witness()") {
        case Apply(_, receiver, MethodIdent(`witnessMethodName`), _) =>
          receiver.tpe == ClassType("Foo")
      }.hasNot("any reference to ObjectClone") {
        case LoadModule(ObjectCloneClass) => true
      }.hasExactly(3, "calls to clone()") {
        case Apply(_, _, MethodIdent(`cloneMethodName`), _) => true
      }
    }
  }

  /** Never inline the `clone()` method of arrays. */
  @Test
  def testCloneOnArrayNotInlined_issue3778(): AsyncResult = await {
    testCloneOnArrayNotInlinedGeneric(List(
        // @inline override def clone(): AnyRef = witness()
        MethodDef(EMF, cloneMethodName, NON, Nil, AnyType, Some {
          Apply(EAF, This()(ClassType("Foo")), witnessMethodName, Nil)(AnyType)
        })(EOH.withInline(true), None)
    ))
  }

  /** Never inline the `clone()` method of arrays, even when the only
   *  reachable `clone()` method is `Object.clone()`.
   */
  @Test
  def testCloneOnArrayNotInlined_issue3778_onlyObjectClone(): AsyncResult = await {
    testCloneOnArrayNotInlinedGeneric(Nil)
  }

  /** Never inline the `clone()` method of arrays, even when `Object.clone()`
   *  and another `clone()` method are reachable.
   */
  @Test
  def testCloneOnArrayNotInlined_issue3778_ObjectCloneAndAnotherClone(): AsyncResult = await {
    testCloneOnArrayNotInlinedGeneric(List(
        // @inline override def clone(): AnyRef = witness()
        MethodDef(EMF, cloneMethodName, NON, Nil, AnyType, Some {
          Block(
              Apply(EAF, This()(ClassType("Foo")), witnessMethodName, Nil)(AnyType),
              ApplyStatically(EAF, This()(ClassType("Foo")),
                  ObjectClass, cloneMethodName, Nil)(AnyType)
          )
        })(EOH.withInline(true), None)
    ))
  }

  /** Makes sure that a hello world does not need java.lang.Class after
   *  optimizations.
   */
  @Test
  def testHelloWorldDoesNotNeedClassClass(): AsyncResult = await {
    val classDefs = Seq(
        mainTestClassDef({
          predefPrintln(StringLiteral("Hello world!"))
        })
    )

    for (linkingUnit <- linkToLinkingUnit(classDefs, MainTestModuleInitializers, TestIRRepo.fulllib)) yield {
      assertFalse(linkingUnit.classDefs.exists(_.className == ClassClass))
    }
  }

  @Test
  def testOptimizerDoesNotEliminateRequiredStaticField_issue4021(): AsyncResult = await {
    val StringType = ClassType(BoxedStringClass)
    val fooGetter = m("foo", Nil, T)
    val classDefs = Seq(
        classDef(
            MainTestClassName,
            kind = ClassKind.Class,
            superClass = Some(ObjectClass),
            memberDefs = List(
                trivialCtor(MainTestClassName),
                // static var foo: java.lang.String
                FieldDef(EMF.withNamespace(PublicStatic).withMutable(true),
                    "foo", NON, StringType),
                // static def foo(): java.lang.String = Test::foo
                MethodDef(EMF.withNamespace(MemberNamespace.PublicStatic),
                    fooGetter, NON, Nil, StringType, Some({
                      SelectStatic(MainTestClassName, "foo")(StringType)
                    }))(EOH, None),
                // static def main(args: String[]) { println(Test::foo()) }
                mainMethodDef({
                  consoleLog(ApplyStatic(EAF, MainTestClassName, fooGetter, Nil)(StringType))
                })
            )
        )
    )

    for (linkingUnit <- linkToLinkingUnit(classDefs, MainTestModuleInitializers)) yield {
      val mainClassDef = linkingUnit.classDefs.find(_.className == MainTestClassName).get
      assertTrue(mainClassDef.fields.exists {
        case FieldDef(_, FieldIdent(name), _, _) => name == FieldName("foo")
        case _                                   => false
      })
    }
  }

}

object OptimizerTest {
  private val cloneMethodName = m("clone", Nil, O)
  private val witnessMethodName = m("witness", Nil, O)

  def linkToLinkingUnit(classDefs: Seq[ClassDef],
      moduleInitializers: List[ModuleInitializer])(
      implicit ec: ExecutionContext): Future[LinkingUnit] = {

    linkToLinkingUnit(classDefs, moduleInitializers, TestIRRepo.minilib)
  }

  def linkToLinkingUnit(classDefs: Seq[ClassDef],
      moduleInitializers: List[ModuleInitializer], stdlib: Future[Seq[IRFile]])(
      implicit ec: ExecutionContext): Future[LinkingUnit] = {

    LinkingUtils.expectSuccess(LinkingUtils.linkToLinkingUnit(
        classDefs, moduleInitializers, StandardConfig(), stdlib))
  }
}
