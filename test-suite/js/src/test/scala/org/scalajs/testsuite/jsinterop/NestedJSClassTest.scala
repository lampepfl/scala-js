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

package org.scalajs.testsuite.jsinterop

import scala.scalajs.js
import scala.scalajs.js.annotation._

import org.junit.Assert._
import org.junit.Test

class NestedJSClassTest {
  import NestedJSClassTest._

  @Test def innerJSClass_basics(): Unit = {
    val container1 = new ScalaClassContainer("hello")
    val innerJSClass = container1.getInnerJSClass
    assertSame(innerJSClass, container1.getInnerJSClass)
    assertSame(innerJSClass, js.constructorOf[container1.InnerJSClass])
    assertEquals("function", js.typeOf(innerJSClass))

    val inner1 = new container1.InnerJSClass("world1")
    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))
    assertTrue(inner1.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner1, innerJSClass))

    val inner2 = js.Dynamic.newInstance(innerJSClass)("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertTrue(inner2.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner2, innerJSClass))

    val container2 = new ScalaClassContainer("hi")
    val innerJSClass2 = container2.getInnerJSClass
    assertNotSame(innerJSClass, innerJSClass2)

    val inner3 = new container2.InnerJSClass("world3")
    assertEquals("hiworld3", inner3.zzz)
    assertEquals("hiworld3foo", inner3.foo("foo"))
    assertTrue(inner3.isInstanceOf[container2.InnerJSClass])
    assertTrue(js.special.instanceof(inner3, container2.getInnerJSClass))

    assertFalse(inner3.isInstanceOf[container1.InnerJSClass])
    assertFalse(js.special.instanceof(inner3, innerJSClass))
  }

  @Test def localJSClass_basics(): Unit = {
    val container1 = new ScalaClassContainer("hello")
    val localJSClass1 = container1.makeLocalJSClass("wide1")
    assertEquals("function", js.typeOf(localJSClass1))

    val inner1 = js.Dynamic.newInstance(localJSClass1)("world1")
    assertEquals("hellowide1world1", inner1.zzz)
    assertEquals("hellowide1world1foo", inner1.foo("foo"))
    assertTrue(js.special.instanceof(inner1, localJSClass1))
    assertFalse(inner1.isInstanceOf[container1.InnerJSClass])

    val inner2 = js.Dynamic.newInstance(localJSClass1)("world2")
    assertEquals("hellowide1world2", inner2.zzz)
    assertEquals("hellowide1world2foo", inner2.foo("foo"))

    val localJSClass2 = container1.makeLocalJSClass("wide2")
    assertNotSame(localJSClass1, localJSClass2)

    val inner3 = js.Dynamic.newInstance(localJSClass2)("world3")
    assertEquals("hellowide2world3", inner3.zzz)
    assertEquals("hellowide2world3foo", inner3.foo("foo"))
    assertTrue(js.special.instanceof(inner3, localJSClass2))
    assertFalse(js.special.instanceof(inner3, localJSClass1))
    assertFalse(inner3.isInstanceOf[container1.InnerJSClass])
  }

  @Test def innerJSClass_basicsInsideTrait(): Unit = {
    val container1 = new ScalaTraitContainerSubclass("hello")
    val innerJSClass = container1.getInnerJSClass
    assertSame(innerJSClass, container1.getInnerJSClass)
    assertSame(innerJSClass, js.constructorOf[container1.InnerJSClass])
    assertEquals("function", js.typeOf(innerJSClass))

    val inner1 = new container1.InnerJSClass("world1")
    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))
    assertTrue(inner1.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner1, innerJSClass))

    val inner2 = js.Dynamic.newInstance(innerJSClass)("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertTrue(inner2.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner2, innerJSClass))

    val container2 = new ScalaTraitContainerSubclass("hi")
    val innerJSClass2 = container2.getInnerJSClass
    assertNotSame(innerJSClass, innerJSClass2)

    val inner3 = new container2.InnerJSClass("world3")
    assertEquals("hiworld3", inner3.zzz)
    assertEquals("hiworld3foo", inner3.foo("foo"))
    assertTrue(inner3.isInstanceOf[container2.InnerJSClass])
    assertTrue(js.special.instanceof(inner3, container2.getInnerJSClass))

    assertFalse(inner3.isInstanceOf[container1.InnerJSClass])
    assertFalse(js.special.instanceof(inner3, innerJSClass))
  }

  @Test def localJSClass_basicsInsideTrait(): Unit = {
    val container1 = new ScalaTraitContainerSubclass("hello")
    val localJSClass1 = container1.makeLocalJSClass("wide1")
    assertEquals("function", js.typeOf(localJSClass1))

    val inner1 = js.Dynamic.newInstance(localJSClass1)("world1")
    assertEquals("hellowide1world1", inner1.zzz)
    assertEquals("hellowide1world1foo", inner1.foo("foo"))
    assertTrue(js.special.instanceof(inner1, localJSClass1))
    assertFalse(inner1.isInstanceOf[container1.InnerJSClass])

    val inner2 = js.Dynamic.newInstance(localJSClass1)("world2")
    assertEquals("hellowide1world2", inner2.zzz)
    assertEquals("hellowide1world2foo", inner2.foo("foo"))

    val localJSClass2 = container1.makeLocalJSClass("wide2")
    assertNotSame(localJSClass1, localJSClass2)

    val inner3 = js.Dynamic.newInstance(localJSClass2)("world3")
    assertEquals("hellowide2world3", inner3.zzz)
    assertEquals("hellowide2world3foo", inner3.foo("foo"))
    assertTrue(js.special.instanceof(inner3, localJSClass2))
    assertFalse(js.special.instanceof(inner3, localJSClass1))
    assertFalse(inner3.isInstanceOf[container1.InnerJSClass])
  }

  @Test def innerJSObject_basics(): Unit = {
    val container1 = new ScalaClassContainerWithObject("hello")
    val inner1 = container1.InnerJSObject
    assertSame(inner1, container1.InnerJSObject)
    assertEquals("object", js.typeOf(inner1))

    assertEquals("hellozzz", inner1.zzz)
    assertEquals("hellozzzfoo", inner1.foo("foo"))
    assertTrue(inner1.isInstanceOf[container1.InnerJSObject.type])

    val container2 = new ScalaClassContainerWithObject("hi")
    val inner2 = container2.InnerJSObject
    assertNotSame(inner1, inner2)
    assertNotSame(inner1.asInstanceOf[js.Dynamic].constructor,
        inner2.asInstanceOf[js.Dynamic].constructor)
    assertEquals("hizzz", inner2.zzz)
    assertEquals("hizzzfoo", inner2.foo("foo"))

    assertFalse(inner2.isInstanceOf[container1.InnerJSObject.type])
  }

  @Test def localJSObject_basics(): Unit = {
    val container1 = new ScalaClassContainerWithObject("hello")
    val inner1 = container1.makeLocalJSObject("world1")

    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))

    val inner2 = container1.makeLocalJSObject("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))

    assertNotSame(inner1, inner2)
    assertNotSame(inner1.asInstanceOf[js.Dynamic].constructor,
        inner2.asInstanceOf[js.Dynamic].constructor)
  }

  @Test def innerJSClassExtendsInnerJSClass(): Unit = {
    val parentsContainer = new ScalaClassContainer("hello")
    val container1 =
      new ScalaClassContainerWithSubclasses("hi", parentsContainer)
    val innerJSClass = parentsContainer.getInnerJSClass
    val innerJSSubclass = container1.getInnerJSSubclass

    val inner1 = new container1.InnerJSSubclass("world1")
    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))
    assertEquals("hiworld1helloworld1", inner1.foobar())

    assertTrue(inner1.isInstanceOf[container1.InnerJSSubclass])
    assertTrue(js.special.instanceof(inner1, innerJSSubclass))
    assertTrue(inner1.isInstanceOf[parentsContainer.InnerJSClass])
    assertTrue(js.special.instanceof(inner1, innerJSClass))

    val container2 =
      new ScalaClassContainerWithSubclasses("salut", parentsContainer)
    val innerJSSubclass2 = container2.getInnerJSSubclass

    val inner2 = js.Dynamic.newInstance(innerJSSubclass2)("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertEquals("salutworld2helloworld2", inner2.foobar())

    assertTrue((inner2: Any).isInstanceOf[container2.InnerJSSubclass])
    assertFalse((inner2: Any).isInstanceOf[container1.InnerJSSubclass])
    assertTrue(js.special.instanceof(inner2, innerJSClass))

    val otherParentsContainer = new ScalaClassContainer("other")
    assertFalse(inner1.isInstanceOf[otherParentsContainer.InnerJSClass])
    assertFalse(inner2.isInstanceOf[otherParentsContainer.InnerJSClass])
  }

  @Test def localJSClassExtendsInnerJSClass(): Unit = {
    val parentsContainer = new ScalaClassContainer("hello")
    val container1 =
      new ScalaClassContainerWithSubclasses("hi", parentsContainer)

    val localJSClass1 = container1.makeLocalJSSubclass("wide1")
    assertEquals("function", js.typeOf(localJSClass1))

    val inner1 = js.Dynamic.newInstance(localJSClass1)("world1")
    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))
    assertEquals("hiwide1helloworld1", inner1.foobar())
    assertTrue(js.special.instanceof(inner1, localJSClass1))
    assertTrue(inner1.isInstanceOf[parentsContainer.InnerJSClass])
    assertFalse(inner1.isInstanceOf[container1.InnerJSSubclass])

    val inner2 = js.Dynamic.newInstance(localJSClass1)("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertEquals("hiwide1helloworld2", inner2.foobar())

    val localJSClass2 = container1.makeLocalJSSubclass("wide2")
    assertNotSame(localJSClass1, localJSClass2)

    val inner3 = js.Dynamic.newInstance(localJSClass2)("world3")
    assertEquals("helloworld3", inner3.zzz)
    assertEquals("helloworld3foo", inner3.foo("foo"))
    assertEquals("hiwide2helloworld3", inner3.foobar())
    assertTrue(js.special.instanceof(inner3, localJSClass2))
    assertTrue(inner3.isInstanceOf[parentsContainer.InnerJSClass])
    assertFalse(js.special.instanceof(inner3, localJSClass1))
    assertFalse(inner3.isInstanceOf[container1.InnerJSSubclass])

    val otherParentsContainer = new ScalaClassContainer("other")
    assertFalse(inner1.isInstanceOf[otherParentsContainer.InnerJSClass])
    assertFalse(inner2.isInstanceOf[otherParentsContainer.InnerJSClass])
    assertFalse(inner3.isInstanceOf[otherParentsContainer.InnerJSClass])
  }

  @Test def innerJSObjectExtendsInnerJSClass(): Unit = {
    val parentsContainer = new ScalaClassContainer("hello")
    val container1 = new ScalaClassContainerWithSubObjects("hi",
        parentsContainer)
    val inner1 = container1.InnerJSObject
    assertSame(inner1, container1.InnerJSObject)
    assertEquals("object", js.typeOf(inner1))

    assertEquals("hellohi", inner1.zzz)
    assertEquals("hellohifoo", inner1.foo("foo"))
    assertEquals("hihellohi", inner1.foobar())
    assertTrue(inner1.isInstanceOf[container1.InnerJSObject.type])
    assertTrue(inner1.isInstanceOf[parentsContainer.InnerJSClass])

    val container2 = new ScalaClassContainerWithSubObjects("hi2",
        parentsContainer)
    val inner2 = container2.InnerJSObject
    assertNotSame(inner1, inner2)
    assertNotSame(inner1.asInstanceOf[js.Dynamic].constructor,
        inner2.asInstanceOf[js.Dynamic].constructor)
    assertEquals("hellohi2", inner2.zzz)
    assertEquals("hellohi2foo", inner2.foo("foo"))
    assertEquals("hi2hellohi2", inner2.foobar())

    assertFalse(inner2.isInstanceOf[container1.InnerJSObject.type])

    val otherParentsContainer = new ScalaClassContainer("other")
    assertFalse(inner1.isInstanceOf[otherParentsContainer.InnerJSClass])
    assertFalse(inner2.isInstanceOf[otherParentsContainer.InnerJSClass])
  }

  @Test def localJSObjectExtendsInnerJSClass(): Unit = {
    val parentsContainer = new ScalaClassContainer("hello")
    val container1 = new ScalaClassContainerWithSubObjects("hi",
        parentsContainer)

    val inner1 = container1.makeLocalJSObject("world1")
    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))
    assertEquals("hiworld1helloworld1", inner1.foobar())
    assertTrue(inner1.isInstanceOf[parentsContainer.InnerJSClass])

    val inner2 = container1.makeLocalJSObject("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertEquals("hiworld2helloworld2", inner2.foobar())
    assertTrue(inner2.isInstanceOf[parentsContainer.InnerJSClass])

    assertNotSame(inner1, inner2)
    assertNotSame(inner1.asInstanceOf[js.Dynamic].constructor,
        inner2.asInstanceOf[js.Dynamic].constructor)

    val otherParentsContainer = new ScalaClassContainer("other")
    assertFalse(inner1.isInstanceOf[otherParentsContainer.InnerJSClass])
    assertFalse(inner2.isInstanceOf[otherParentsContainer.InnerJSClass])
  }

  @Test def convolutedGenericTypeParametersInSuperClass(): Unit = {
    val parentsContainer = new GenericJSSuperClassContainer
    val container1 = new ScalaClassContainerWithTypeParameters[Int](5,
        parentsContainer)

    type MyB = List[List[Int]]

    val innerJSClass = js.constructorOf[container1.GenericJSInnerClass[MyB]]
    assertSame(innerJSClass,
        js.constructorOf[container1.GenericJSInnerClass[MyB]])
    assertEquals("function", js.typeOf(innerJSClass))
    val inner: Any = new container1.GenericJSInnerClass[MyB](Nil)
    assertTrue(inner.isInstanceOf[parentsContainer.GenericJSSuperClass[_, _]])

    val localJSClass = container1.makeGenericJSLocalClass()
    assertNotSame(localJSClass, container1.makeGenericJSLocalClass())
    assertEquals("function", js.typeOf(localJSClass))
    val local: Any = js.Dynamic.newInstance(localJSClass)(Nil.asInstanceOf[js.Any])
    assertTrue(local.isInstanceOf[parentsContainer.GenericJSSuperClass[_, _]])

    val innerJSObject = container1.GenericJSInnerObject
    assertSame(innerJSObject, container1.GenericJSInnerObject)
    assertTrue(innerJSObject.isInstanceOf[parentsContainer.GenericJSSuperClass[_, _]])

    val localJSObject = container1.makeGenericJSInnerObject(Nil)
    assertNotSame(localJSObject, container1.makeGenericJSInnerObject(Nil))
    assertTrue(localJSObject.isInstanceOf[parentsContainer.GenericJSSuperClass[_, _]])
  }

  @Test def innerJSClass_basicsInsideJSClass(): Unit = {
    val container1 = new JSClassContainer("hello")
    val innerJSClass = container1.getInnerJSClass
    assertSame(innerJSClass, container1.getInnerJSClass)
    assertSame(innerJSClass, js.constructorOf[container1.InnerJSClass])
    assertEquals("function", js.typeOf(innerJSClass))

    val inner1 = new container1.InnerJSClass("world1")
    assertEquals("helloworld1", inner1.zzz)
    assertEquals("helloworld1foo", inner1.foo("foo"))
    assertTrue(inner1.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner1, innerJSClass))

    val inner2 = js.Dynamic.newInstance(innerJSClass)("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertTrue(inner2.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner2, innerJSClass))

    val container2 = new JSClassContainer("hi")
    val innerJSClass2 = container2.getInnerJSClass
    assertNotSame(innerJSClass, innerJSClass2)

    val inner3 = new container2.InnerJSClass("world3")
    assertEquals("hiworld3", inner3.zzz)
    assertEquals("hiworld3foo", inner3.foo("foo"))
    assertTrue(inner3.isInstanceOf[container2.InnerJSClass])
    assertTrue(js.special.instanceof(inner3, container2.getInnerJSClass))

    assertFalse(inner3.isInstanceOf[container1.InnerJSClass])
    assertFalse(js.special.instanceof(inner3, innerJSClass))
  }

  @Test def innerJSClass_accessibleFromJS_ifInsideJSClass(): Unit = {
    val container1 = new JSClassContainer("hello")
    val innerJSClass = container1.asInstanceOf[js.Dynamic].getInnerJSClass
    assertSame(innerJSClass, container1.getInnerJSClass)
    assertSame(innerJSClass, js.constructorOf[container1.InnerJSClass])
    assertEquals("function", js.typeOf(innerJSClass))

    val inner2 = js.Dynamic.newInstance(innerJSClass)("world2")
    assertEquals("helloworld2", inner2.zzz)
    assertEquals("helloworld2foo", inner2.foo("foo"))
    assertTrue(inner2.isInstanceOf[container1.InnerJSClass])
    assertTrue(js.special.instanceof(inner2, innerJSClass))

    val container2 = new JSClassContainer("hi")
    val innerJSClass2 = container2.asInstanceOf[js.Dynamic].getInnerJSClass
    assertNotSame(innerJSClass, innerJSClass2)

    val inner3 = js.Dynamic.newInstance(innerJSClass2)("world3")
    assertEquals("hiworld3", inner3.zzz)
    assertEquals("hiworld3foo", inner3.foo("foo"))
    assertTrue(inner3.isInstanceOf[container2.InnerJSClass])
    assertTrue(js.special.instanceof(inner3, container2.getInnerJSClass))

    assertFalse(inner3.isInstanceOf[container1.InnerJSClass])
    assertFalse(js.special.instanceof(inner3, innerJSClass))
  }

  @Test def localJSClassCapturesCharThatMustBeBoxed(): Unit = {
    @inline def makeChar(): Any = 'A'

    val char = makeChar()

    class LocalJSClassWithCharCapture extends js.Object {
      def getCharAny(): Any = char
      def getCharAsChar(): Char = char.asInstanceOf[Char]
    }

    val obj = new LocalJSClassWithCharCapture
    val charAny = obj.getCharAny()
    assertTrue(charAny.toString(), charAny.isInstanceOf[Char])
    assertEquals('A', charAny)
    assertEquals("A", charAny.toString())
    assertEquals('A', obj.getCharAsChar())
  }

  @Test def overloadedConstructorsInLocalJSClass(): Unit = {
    val a = 5
    val b = 10

    class LocalJSClassWithOverloadedConstructors(val x: Int) extends js.Object {
      val aa = a

      def this(x: Int, y: Int) = {
        this(x + y + b)
      }
    }

    val obj1 = new LocalJSClassWithOverloadedConstructors(50)
    assertEquals(50, obj1.x)
    assertEquals(5, obj1.aa)

    val obj2 = new LocalJSClassWithOverloadedConstructors(34, 78)
    assertEquals(34 + 78 + 10, obj2.x)
    assertEquals(5, obj2.aa)
  }

  @Test def selfReferencingLocalJSClass(): Unit = {
    class JSCons[+A](val head: A, val tail: JSCons[A]) extends js.Object {
      def ::[B >: A](x: B): JSCons[B] =
        new JSCons[B](x, this)

      def self: js.Dynamic = js.constructorOf[JSCons[_]]
    }

    val threeAndNil = new JSCons(3, null)
    val list = "head" :: 2 :: threeAndNil

    assertEquals(js.constructorOf[JSCons[_]], list.self)
    assertEquals("head", list.head)
    assertEquals(2, list.tail.head)
    assertEquals(3, list.tail.tail.head)
    assertNull(list.tail.tail.tail)
  }

}

object NestedJSClassTest {
  trait TestInterface extends js.Object {
    val zzz: String

    def foo(a: String): String
  }

  class ScalaClassContainer(xxx: String) {
    class InnerJSClass(yyy: String) extends js.Object with TestInterface {
      val zzz: String = xxx + yyy

      def foo(a: String): String = xxx + yyy + a
    }

    def getInnerJSClass: js.Dynamic =
      js.constructorOf[InnerJSClass]

    def makeLocalJSClass(yyy: String): js.Dynamic = {
      class LocalJSClass(abc: String) extends js.Object with TestInterface {
        val zzz: String = xxx + yyy + abc

        def foo(a: String): String = xxx + yyy + abc + a
      }

      js.constructorOf[LocalJSClass]
    }
  }

  trait ScalaTraitContainer {
    def xxx: String

    class InnerJSClass(yyy: String) extends js.Object with TestInterface {
      val zzz: String = xxx + yyy

      def foo(a: String): String = xxx + yyy + a
    }

    def getInnerJSClass: js.Dynamic =
      js.constructorOf[InnerJSClass]

    def makeLocalJSClass(yyy: String): js.Dynamic = {
      class LocalJSClass(abc: String) extends js.Object with TestInterface {
        val zzz: String = xxx + yyy + abc

        def foo(a: String): String = xxx + yyy + abc + a
      }

      js.constructorOf[LocalJSClass]
    }
  }

  class ScalaTraitContainerSubclass(val xxx: String) extends ScalaTraitContainer

  class ScalaClassContainerWithObject(xxx: String) {
    object InnerJSObject extends js.Object with TestInterface {
      val zzz: String = xxx + "zzz"

      def foo(a: String): String = xxx + "zzz" + a
    }

    def makeLocalJSObject(yyy: String): TestInterface = {
      object LocalJSObject extends js.Object with TestInterface {
        val zzz: String = xxx + yyy

        def foo(a: String): String = xxx + yyy + a
      }

      LocalJSObject
    }
  }

  class ScalaClassContainerWithSubclasses(val abc: String,
      val parents: ScalaClassContainer) {

    class InnerJSSubclass(yyy: String) extends parents.InnerJSClass(yyy) {
      def foobar(): String = abc + yyy + zzz
    }

    def getInnerJSSubclass: js.Dynamic =
      js.constructorOf[InnerJSSubclass]

    def makeLocalJSSubclass(yyy: String): js.Dynamic = {
      class LocalJSSubclass(xyz: String) extends parents.InnerJSClass(xyz) {
        def foobar(): String = abc + yyy + zzz
      }
      js.constructorOf[LocalJSSubclass]
    }
  }

  class ScalaClassContainerWithSubObjects(val abc: String,
      val parents: ScalaClassContainer) {

    object InnerJSObject extends parents.InnerJSClass(abc) {
      def foobar(): String = abc + zzz
    }

    def makeLocalJSObject(yyy: String): js.Dynamic = {
      object LocalJSObject extends parents.InnerJSClass(yyy) {
        def foobar(): String = abc + yyy + zzz
      }
      LocalJSObject.asInstanceOf[js.Dynamic]
    }
  }

  class GenericJSSuperClassContainer {
    class GenericJSSuperClass[A, B <: List[Seq[A]]](val a: A, val b: B)
        extends js.Object
  }

  class ScalaClassContainerWithTypeParameters[A](val a: A,
      val parents: GenericJSSuperClassContainer) {

    class GenericJSInnerClass[B <: List[Seq[A]]](b: B)
        extends parents.GenericJSSuperClass[A, B](a, b)

    def makeGenericJSLocalClass(): js.Dynamic = {
      class GenericJSLocalClass[B <: List[Seq[A]]](b: B)
          extends parents.GenericJSSuperClass[A, B](a, b)
      js.constructorOf[GenericJSLocalClass[_]]
    }

    object GenericJSInnerObject
        extends parents.GenericJSSuperClass[A, List[List[A]]](a, Nil)

    def makeGenericJSInnerObject[B <: List[Seq[A]]](b: B): js.Dynamic = {
      object GenericJSInnerObject
          extends parents.GenericJSSuperClass[A, B](a, b)

      GenericJSInnerObject.asInstanceOf[js.Dynamic]
    }
  }

  class JSClassContainer(xxx: String) extends js.Object {
    class InnerJSClass(yyy: String) extends js.Object with TestInterface {
      val zzz: String = xxx + yyy

      def foo(a: String): String = xxx + yyy + a
    }

    def getInnerJSClass: js.Dynamic =
      js.constructorOf[InnerJSClass]
  }

}
