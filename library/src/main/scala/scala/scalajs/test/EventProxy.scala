package scala.scalajs.test

import scala.scalajs.js

trait EventProxy extends js.Object {

  def error(message: js.String, stack: js.Array[js.Dictionary]): Unit = ???
  def failure(message: js.String, stack: js.Array[js.Dictionary]): Unit = ???
  def succeeded(message: js.String): Unit = ???
  def skipped(message: js.String): Unit = ???
  def pending(message: js.String): Unit = ???
  def ignored(message: js.String): Unit = ???
  def canceled(message: js.String): Unit = ???

  def error(message: js.String): Unit = ???
  def info(message: js.String): Unit = ???
}
