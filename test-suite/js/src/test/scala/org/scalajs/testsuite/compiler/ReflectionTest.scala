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

package org.scalajs.testsuite.compiler

import scala.language.implicitConversions

import java.lang.Cloneable
import java.io.Serializable

import scala.reflect.{classTag, ClassTag}

import scala.scalajs.js
import js.annotation.JSGlobal

import org.junit.Test
import org.junit.Assert._
import org.junit.Assume._

import org.scalajs.testsuite.utils.AssertThrows._
import org.scalajs.testsuite.utils.Platform._

/** Tests the little reflection we support */
class ReflectionTest {
  import ReflectionTest._

  def implicitClassTagTest[A: ClassTag](x: Any): Boolean = x match {
    case x: A => true
    case _    => false
  }

  @Test def java_lang_Class_getName_under_normal_circumstances(): Unit = {
    @noinline
    def testNoInline(expected: String, cls: Class[_]): Unit =
      assertEquals(expected, cls.getName())

    @inline
    def test(expected: String, cls: Class[_]): Unit = {
      testNoInline(expected, cls)
      assertEquals(expected, cls.getName())
    }

    test("scala.Some", classOf[scala.Some[_]])
  }

  @Test def should_append_$_to_class_name_of_objects(): Unit = {
    assertEquals("org.scalajs.testsuite.compiler.ReflectionTest$TestObject$",
        TestObject.getClass.getName)
  }

  @Test def java_lang_Class_getName_renamed_through_semantics(): Unit = {
    @noinline
    def testNoInline(expected: String, cls: Class[_]): Unit =
      assertEquals(expected, cls.getName())

    @inline
    def test(expected: String, cls: Class[_]): Unit = {
      testNoInline(expected, cls)
      assertEquals(expected, cls.getName())
    }

    test("renamed.test.Class", classOf[RenamedTestClass])
    test("renamed.test.byprefix.RenamedTestClass1", classOf[PrefixRenamedTestClass1])
    test("renamed.test.byprefix.RenamedTestClass2", classOf[PrefixRenamedTestClass2])
    test("renamed.test.byotherprefix.RenamedTestClass", classOf[OtherPrefixRenamedTestClass])
  }

  @Test def java_lang_Object_getClass_getName_renamed_through_semantics(): Unit = {
    // x.getClass().getName() is subject to optimizations

    @noinline
    def getClassOfNoInline(x: Any): Class[_] =
      x.getClass()

    @noinline
    def testNoInline(expected: String, x: Any): Unit = {
      assertEquals(expected, getClassOfNoInline(x).getName())
      assertEquals(expected, x.getClass().getName())
    }

    @inline
    def test(expected: String, x: Any): Unit = {
      testNoInline(expected, x)
      assertEquals(expected, x.getClass().getName())
    }

    test("renamed.test.Class", new RenamedTestClass)
    test("renamed.test.byprefix.RenamedTestClass1", new PrefixRenamedTestClass1)
    test("renamed.test.byprefix.RenamedTestClass2", new PrefixRenamedTestClass2)
    test("renamed.test.byotherprefix.RenamedTestClass", new OtherPrefixRenamedTestClass)
  }

  @Test def should_support_isInstance(): Unit = {
    class A
    class B extends A
    val b = new B
    assertTrue(classOf[A].isInstance(b))
    assertFalse(classOf[A].isInstance("hello"))

    assertTrue(classOf[Array[Seq[_]]].isInstance(Array(List(3))))

    assertTrue(classOf[Serializable].isInstance(1))
    assertTrue(classOf[Serializable].isInstance(1.4))
    assertTrue(classOf[Serializable].isInstance(true))
    assertTrue(classOf[Serializable].isInstance('Z'))
    assertTrue(classOf[Serializable].isInstance("hello"))

    assertTrue(classOf[Serializable].isInstance(new Array[Int](1)))
    assertTrue(classOf[Cloneable].isInstance(new Array[Int](1)))
    assertTrue(classOf[Serializable].isInstance(new Array[String](1)))
    assertTrue(classOf[Cloneable].isInstance(new Array[String](1)))
  }

  @Test def isInstance_for_JS_class(): Unit = {
    js.eval("""var ReflectionTestJSClass = (function() {})""")

    val obj = new ReflectionTestJSClass
    assertTrue(obj.isInstanceOf[ReflectionTestJSClass])
    assertTrue(classOf[ReflectionTestJSClass].isInstance(obj))

    val other = (5, 6): Any
    assertFalse(other.isInstanceOf[ReflectionTestJSClass])
    assertFalse(classOf[ReflectionTestJSClass].isInstance(other))

    val ct = classTag[ReflectionTestJSClass]
    assertTrue(ct.unapply(obj).isDefined)
    assertFalse(ct.unapply(other).isDefined)

    assertTrue(implicitClassTagTest[ReflectionTestJSClass](obj))
    assertFalse(implicitClassTagTest[ReflectionTestJSClass](other))
  }

  @Test def isInstance_for_JS_traits_should_fail(): Unit = {
    assertThrows(classOf[Exception], classOf[ReflectionTestJSTrait].isInstance(5))

    val ct = classTag[ReflectionTestJSTrait]
    assertThrows(classOf[Exception], ct.unapply(new AnyRef))

    assertThrows(classOf[Exception], implicitClassTagTest[ReflectionTestJSTrait](new AnyRef))
  }

  @Test def getClass_for_normal_types(): Unit = {
    class Foo {
      def bar(): Class[_] = super.getClass()
    }
    val foo = new Foo
    assertSame(foo.getClass(), classOf[Foo])
    assertSame(foo.bar(), classOf[Foo])
  }

  @Test def getClass_for_anti_boxed_primitive_types(): Unit = {
    implicit def classAsAny(c: java.lang.Class[_]): js.Any =
      c.asInstanceOf[js.Any]
    assertEquals(classOf[java.lang.Boolean], (false: Any).getClass)
    assertEquals(classOf[java.lang.Character], ('a': Any).getClass)
    assertEquals(classOf[java.lang.Byte], (1.toByte: Any).getClass)
    assertEquals(classOf[java.lang.Byte], (1.toShort: Any).getClass)
    assertEquals(classOf[java.lang.Byte], (1: Any).getClass)
    assertEquals(classOf[java.lang.Long], (1L: Any).getClass)
    assertEquals(classOf[java.lang.Float], (1.5f: Any).getClass)
    assertEquals(classOf[java.lang.Float], (1.5: Any).getClass)
    assertEquals(classOf[scala.runtime.BoxedUnit], ((): Any).getClass)
  }

  @Test def getSuperclass_issue_1489(): Unit = {
    assertEquals(classOf[SomeParentClass], classOf[SomeChildClass].getSuperclass)
    assertNull(classOf[AnyRef].getSuperclass)
    assertEquals(classOf[AnyRef], classOf[String].getSuperclass)
    assertEquals(classOf[Number], classOf[Integer].getSuperclass)

    assertEquals(
        "org.scalajs.testsuite.compiler.ReflectionTest$ParentClassWhoseDataIsNotAccessedDirectly",
        classOf[ChildClassWhoseDataIsAccessedDirectly].getSuperclass.getName)
  }

  @Test def cast_positive(): Unit = {
    assertNull(classOf[String].cast(null))
    assertEquals("hello", classOf[String].cast("hello"))
    assertEquals(List(1, 2), classOf[Seq[_]].cast(List(1, 2)))
    classOf[Serializable].cast(Array(3)) // should not throw
    classOf[Cloneable].cast(Array(3)) // should not throw
    classOf[Object].cast(js.Array(3, 4)) // should not throw
  }

  @Test def cast_negative(): Unit = {
    assumeTrue("Assumed compliant asInstanceOf", hasCompliantAsInstanceOfs)
    assertThrows(classOf[Exception], classOf[String].cast(5))
    assertThrows(classOf[Exception], classOf[Seq[_]].cast(Some("foo")))
  }
}

object ReflectionTest {
  object TestObject

  class RenamedTestClass

  class PrefixRenamedTestClass1
  class PrefixRenamedTestClass2

  class OtherPrefixRenamedTestClass

  @JSGlobal("ReflectionTestJSClass")
  @js.native
  class ReflectionTestJSClass extends js.Object

  @js.native
  trait ReflectionTestJSTrait extends js.Object

  class SomeParentClass
  class SomeChildClass extends SomeParentClass

  class ParentClassWhoseDataIsNotAccessedDirectly
  class ChildClassWhoseDataIsAccessedDirectly extends ParentClassWhoseDataIsNotAccessedDirectly

}
