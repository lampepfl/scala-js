/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, Jonas Fonseca    **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package scala.scalajs.js

import scala.scalajs.js
import scala.scalajs.test.ScalaJSTest

object DictionaryTest extends ScalaJSTest {

  describe("scala.scalajs.js.Dictionary") {

    it("should provide equivalent of JS for-in loop of {} - #13") {
      val obj = js.eval("var dictionaryTest13 = { a: 'Scala.js', b: 7357 }; dictionaryTest13;")
      val dict: js.Dictionary = obj
      var propCount = 0
      var propString = ""

      for (prop <- js.Dictionary.propertiesOf(dict)) {
        propCount += 1
        propString += dict(prop)
      }

      expect(propCount).toEqual(2)
      expect(propString).toEqual("Scala.js7357")
    }

    it("should provide equivalent of JS for-in loop of [] - #13") {
      val obj = js.eval("var arrayTest13 = [ 7, 3, 5, 7 ]; arrayTest13;")
      val array: js.Dictionary = obj
      var propCount = 0
      var propString = ""

      for (prop <- js.Dictionary.propertiesOf(array)) {
        propCount += 1
        propString += array(prop)
      }

      expect(propCount).toEqual(4)
      expect(propString).toEqual("7357")
    }

  }
}
