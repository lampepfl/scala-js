package org.scalajs.jasmine

import scala.scalajs.js

object Jasmine extends js.GlobalScope {
  def jasmine: JasmineEnv = ???
  def describe(name: String, suite: js.Function0[_]): Unit = ???
  def it(title: String, test: js.Function0[_]): Unit = ???
  def xdescribe(name: String, suite: js.Function0[_]): Unit = ???
  def xit(title: String, test: js.Function0[_]): Unit = ???
  def beforeEach(block: js.Function0[_]): Unit = ???
  def afterEach(block: js.Function0[_]): Unit = ???
  def expect(exp: js.Any): JasmineExpectation = ???
  def runs(block: js.Function0[_]): Unit = ???
  def waits(timeout: Int): Unit = ???
  def waitsFor(block: js.Function0[Boolean], errorMsg: String, timeout: Int): Unit = ???
}
