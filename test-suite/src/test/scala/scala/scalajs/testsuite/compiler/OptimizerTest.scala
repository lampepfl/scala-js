/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package scala.scalajs.testsuite.compiler

import org.scalajs.jasminetest.JasmineTest

object OptimizerTest extends JasmineTest {

  describe("Inlineable classes") {

    it("must update fields of `this` in the computation of other fields - #1153") {
      val foo = new InlineClassDependentFields(5)
      expect(foo.x).toEqual(5)
      expect(foo.b).toBeTruthy
      expect(foo.y).toEqual(11)
    }

    it("must not break code that assigns `this` to a field") {
      val foo = new InlineClassThisAlias(5)
      expect(foo.z).toEqual(5)
    }

  }

  @inline
  class InlineClassDependentFields(val x: Int) {
    val b = x > 3
    val y = if (b) x + 6 else x-2
  }

  @inline
  class InlineClassThisAlias(val x: Int) {
    val t = this
    val y = x
    val z = t.y
  }

}
