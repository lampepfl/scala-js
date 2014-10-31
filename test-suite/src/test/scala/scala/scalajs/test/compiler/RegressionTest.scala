/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package scala.scalajs.test
package compiler

import scala.annotation.tailrec

import scala.scalajs.js
import scala.scalajs.test.JasmineTest

object RegressionTest extends JasmineTest {

  class Bug218Foo[T](val x: T) extends AnyVal

  describe("Scala.js compiler regression tests") {

    it("Wrong division conversion (7 / 2.0) - #18") {
      val div = 7 / 2.0
      expect(div).toEqual(3.5)
      expect(div.getClass.getName).toEqual("double")

      val mod = 7 % 2.0
      expect(mod).toEqual(1.0)
      expect(mod.getClass.getName).toEqual("double")
    }

    it("js.prim.String + js.prim.String is ambiguous - #20") {
      val a: js.prim.String = "a"
      val b: js.prim.String = "b"
      val c: js.prim.String = a + b
      expect(c).toEqual("ab")
    }

    it("Abort with some pattern match guards - #22") {
      object PatternMatchGuards {
        def go(f: Int => Int) = f(1)
        def main(): Unit = {
          go {
            case x if false => x
          }
        }
      }
      // Nothing to check
    }

    it("Bad encoding for characters spanning 2 UTF-16 chars - #23") {
      val str = "A∀\uD835\uDCAB"
      var s: String = ""
      for (c <- str) {
        val code: Int = c
        s = s + code + " "
      }
      expect(s).toEqual("65 8704 55349 56491 ")
    }

    it("String concatenation with null - #26") {
      val x: Object = null
      expect(x + "check").toEqual("nullcheck")
    }

    class Bug66A(s: String, e: Object) {
      def this(e: Object) = this("", e)
      def this(s: String) = this(s, "")
    }
    class Bug66B(s: String, e: Object) extends Bug66A(s)

    it("should emit static calls when forwarding to another constructor - #66") {
      new Bug66B("", "")
    }

    it("should not swallow Unit expressions when converting to js.prim.Undefined - #83") {
      var effectHappened = false
      def doEffect(): Unit = effectHappened = true
      def f(): js.prim.Undefined = doEffect()
      f()
      expect(effectHappened).toBeTruthy
    }

    it("should correctly call subSequence on non-string CharSequences - #55") {
      val arr: CharSequence = Array('a','b','c','d')
      val ss = arr.subSequence(2,3)
      expect(ss.length()).toEqual(1)
      expect(ss.charAt(0)).toEqual('c')
    }

    it("should correctly concat primitive values to strings - #113") {
      expect(4 + "foo").toEqual("4foo")
      expect('a' + "foo").toEqual("afoo")
    }

    it("should resolve overloads on scala.Function.apply when converting to js.Function - #125") {
      class Fct extends Function1[Int,Any] {
        def apply(n: Int) = n
      }

      val scalaFunction = new Fct
      val jsFunction: js.Any = scalaFunction
      val thisFunction: js.ThisFunction = scalaFunction
    }

    it("should correctly dispatch calls on private functions - #165") {
      class A {
        private def x = 1
        def value = x
      }
      class B extends A {
        private def x = 2
      }
      expect(new B().value).toEqual(1)
    }

    it("should correctly mangle JavaScript reserved identifiers - #153") {
      // Class name
      class break {
        // class variable
        var continue = 1
        // method name
        def switch = {
          // local name
          val default = 2
          default
        }
      }
      trait Foo {
        // static member (through mixin)
        def function = 3
      }

      val x = new break with Foo
      expect(x.continue).toEqual(1)
      expect(x.switch).toEqual(2)
      expect(x.function).toEqual(3)
    }

    it("should correctly mangle identifiers starting with a digit - #153") {
      // Class name
      class `0` {
        // class variable
        var `1` = 1
        // method name
        def `2` = {
          // local name
          val `22` = 2
          `22`
        }
      }
      trait Foo {
        // static member (through mixin)
        def `3` = 3
      }

      val x = new `0` with Foo
      expect(x.`1`).toEqual(1)
      expect(x.`2`).toEqual(2)
      expect(x.`3`).toEqual(3)
    }

    it("should reserve `eval` and `arguments` - #743") {
      val eval = 5
      expect(eval).toEqual(5)
      val arguments = "hello"
      expect(arguments).toEqual("hello")
    }

    it("should support class literals for existential value types - #218") {
      expect(scala.reflect.classTag[Bug218Foo[_]].toString).toEqual(
          "scala.scalajs.test.compiler.RegressionTest$Bug218Foo")
    }

    it("should support Buffer - #268") {
      val a = scala.collection.mutable.Buffer.empty[Int]
      a.insert(0, 0)
      a.remove(0)
      for (i <- 0 to 10) {
        a.insert(a.length / 2, i)
      }
      expect(a.mkString(", ")).toEqual("1, 3, 5, 7, 9, 10, 8, 6, 4, 2, 0")
    }

    it("should not call equals when comparing with a literal null - #362") {
      class A { override def equals(x: Any) = !(this == null) }

      val x = new A
      val y = new A

      // If the null comparisons actually call equals, the following two will
      // cause infinite recursion
      expect(x == y).toBeTruthy
      expect(y == x).toBeTruthy
    }

    it("should unbox null to the zero of types - #674") {
      class Box[A] {
        var value: A = _
      }
      def zero[A]: A = new Box[A].value

      /* Note: the same shape of test for Unit does not work, but it seems to
       * be a problem in scalac because it does not work on the JVM either.
       */

      val bool = zero[Boolean]
      expect((bool: Any).isInstanceOf[Boolean]).toBeTruthy
      expect(bool == false).toBeTruthy

      val char = zero[Char]
      expect((char: Any).isInstanceOf[Char]).toBeTruthy
      expect(char == '\u0000').toBeTruthy

      val byte = zero[Byte]
      expect((byte: Any).isInstanceOf[Byte]).toBeTruthy
      expect(byte == 0.toByte).toBeTruthy

      val short = zero[Short]
      expect((short: Any).isInstanceOf[Short]).toBeTruthy
      expect(short == 0.toShort).toBeTruthy

      val int = zero[Int]
      expect((int: Any).isInstanceOf[Int]).toBeTruthy
      expect(int == 0).toBeTruthy

      val long = zero[Long]
      expect((long: Any).isInstanceOf[Long]).toBeTruthy
      expect(long == 0L).toBeTruthy

      val float = zero[Float]
      expect((float: Any).isInstanceOf[Float]).toBeTruthy
      expect(float == 0.0f).toBeTruthy

      val double = zero[Double]
      expect((double: Any).isInstanceOf[Double]).toBeTruthy
      expect(double == 0.0).toBeTruthy

      val ref = zero[AnyRef]
      expect(ref == null).toBeTruthy
    }

    it("Param defs in tailrec methods should be considered mutable - #825") {
      @tailrec
      def foo(x: Int, y: Int): Unit = {
        if (x < y) foo(y, x)
        else {
          expect(x).toEqual(4)
          expect(y).toEqual(2)
        }
      }
      foo(2, 4)
    }

    it("null.synchronized should throw - #874") {
      expect(() => null.synchronized(5)).toThrow
    }

    it("x.synchronized should preserve side-effects of x") {
      var c = 0
      def x = { c += 1; this }
      expect(x.synchronized(5)).toEqual(5)
      expect(c).toEqual(1)
    }

    it("IR checker should allow Apply/Select on NullType and NothingType - #1123") {
      def giveMeANull(): Null = null
      expect(() => (giveMeANull(): StringBuilder).append(5)).toThrow
      expect(() => (giveMeANull(): scala.runtime.IntRef).elem).toThrow

      def giveMeANothing(): Nothing = sys.error("boom")
      expect(() => (giveMeANothing(): StringBuilder).append(5)).toThrow
      expect(() => (giveMeANothing(): scala.runtime.IntRef).elem).toThrow
    }
  }
}
