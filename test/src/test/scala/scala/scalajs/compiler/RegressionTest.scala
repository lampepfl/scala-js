/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, Jonas Fonseca    **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package scala.scalajs.compiler

import scala.scalajs.js
import scala.scalajs.test.ScalaJSTest

object RegressionTest extends ScalaJSTest {

  describe("Scala.js compiler regression tests") {

    it("Wrong division conversion (7 / 2.0) - #18") {
      val div = 7 / 2.0
      expect(div).toEqual(3.5)
      expect(div.getClass.getName).toEqual("double")

      val mod = 7 % 2.0
      expect(mod).toEqual(1.0)
      expect(mod.getClass.getName).toEqual("double")
    }

    it("js.String + js.String is ambiguous - #20") {
      val a: js.String = "a"
      val b: js.String = "b"
      val c: js.String = a + b
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

  }
}
