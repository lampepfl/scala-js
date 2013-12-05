/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js API               **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-lang.org/     **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */



package scala.scalajs

/** Contains primitive types for interoperability with JavaScript libraries.
 *  This package is only relevant to the Scala.js compiler, and should not be
 *  referenced by any project compiled to the JVM.
 *
 *  All the values and methods in this package object are representatives of
 *  standard variables and functions available in the top-level scope, as
 *  standardized in ECMAScript 5.1.
 *
 *  == Guide ==
 *
 *  General documentation on Scala.js can is available at
 *  [[http://lampwww.epfl.ch/~doeraene/scala-js/doc/]].
 *
 *  == Overview ==
 *
 *  The trait [[js.Any]] is the super type of all JavaScript values. It has
 *  subtraits [[js.Number]], [[js.Boolean]], [[js.String]] and [[js.Undefined]]
 *  which represent values of primitive JavaScript types. It also has a
 *  subclass [[js.Object]], which is the base class of all JavaScript objects,
 *  and represents the predefined `Object` class of JavaScript.
 *
 *  All class, trait and object definitions that inherit, directly or
 *  indirectly, from [[js.Any]] do not have actual implementations in Scala.
 *  They are only the manifestation of static types representing libraries
 *  written directly in JavaScript. It is not possible to implement yourself
 *  a subclass of [[js.Any]]: all the method definitions will be ignored when
 *  compiling to JavaScript.
 *
 *  The trait [[js.Dynamic]] is a special subtrait of [[js.Any]]. It can
 *  represent any JavaScript value in a dynamically typed way. It is possible
 *  to call any method and read and write any field of a value of type
 *  [[js.Dynamic]].
 *
 *  The trait [[js.Dictionary]] provides read and write access to any field of
 *  any JavaScript value with the array access syntax of Scala, mapping to the
 *  array access syntax of JavaScript.
 */
package object js extends js.GlobalScope {
  /** The constant Not-a-Number. */
  val NaN: Number = ???
  /** The constant Positive Infinity. */
  val Infinity: Number = ???

  /** Evaluates JavaScript code and returns the result. */
  def eval(x: String): Any = ???

  /** Parses a string as an integer with a given radix. */
  def parseInt(s: String, radix: Number): Number = ???
  /** Parses a string as an integer with auto-detected radix. */
  def parseInt(s: String): Number = ???
  /** Parses a string as a floating point number. */
  def parseFloat(string: String): Number = ???

  /** Tests whether the given value is Not-a-Number. */
  def isNaN(number: Number): Boolean = ???
  /** Tests whether the given value is a finite number. */
  def isFinite(number: Number): Boolean = ???

  /** Decodes a Uniform Resource Identifier (URI).
   *  @see [[encodeURI]]
   */
  def decodeURI(encodedURI: String): String = ???

  /** Decodes a Uniform Resource Identifier (URI) component.
   *  @see [[encodeURIComponent]]
   */
  def decodeURIComponent(encodedURIComponent: String): String = ???

  /** Encodes a Uniform Resource Identifier (URI).
   *  @see [[decodeURI]]
   */
  def encodeURI(uri: String): String = ???

  /** Encodes a Uniform Resource Identifier (URI) component.
   *  @see [[decodeURIComponent]]
   */
  def encodeURIComponent(uriComponent: String): String = ???

  type String = java.lang.String
}
