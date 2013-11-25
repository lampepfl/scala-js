/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, Jonas Fonseca    **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package scala.scalajs.test

import scala.scalajs.js
import java.util.regex.Pattern

trait JasmineExpectation extends js.Object {
  def toBe(exp: js.Any): Unit
  def toEqual(exp: js.Any): Unit
  def toMatch(exp: Pattern): Unit
  def toMatch(exp: String): Unit = toMatch(Pattern.compile(exp))
  def toBeDefined(): Unit
  def toBeUndefined(): Unit
  def toBeNull(): Unit
  def toBeTruthy(): Unit
  def toBeFalsy(): Unit
  def toContain(exp: js.Any): Unit
  def toBeLessThan(exp: js.Number): Unit
  def toBeCloseTo(exp: js.Number): Unit
  def toThrow(): Unit
  val not: JasmineExpectation
}
