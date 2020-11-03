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

package java.lang

import scala.language.implicitConversions

import scala.scalajs.js
import scala.scalajs.js.annotation.JSBracketAccess

private[lang] object Utils {
  @inline
  def isUndefined(x: Any): scala.Boolean =
    x.asInstanceOf[AnyRef] eq ().asInstanceOf[AnyRef]

  @inline
  def undefOrIsDefined[A](x: js.UndefOr[A]): scala.Boolean =
    x ne ().asInstanceOf[AnyRef]

  @inline
  def undefOrForceGet[A](x: js.UndefOr[A]): A =
    x.asInstanceOf[A]

  @inline
  def undefOrGetOrElse[A](x: js.UndefOr[A], default: A): A =
    if (undefOrIsDefined(x)) undefOrForceGet(x)
    else default

  @inline
  def undefOrGetOrElseCompute[A](x: js.UndefOr[A])(default: js.Function0[A]): A =
    if (undefOrIsDefined(x)) undefOrForceGet(x)
    else default()

  @inline
  def undefOrFold[A, B](x: js.UndefOr[A])(default: B, f: js.Function1[A, B]): B =
    if (undefOrIsDefined(x)) f(undefOrForceGet(x))
    else default

  private object Cache {
    val safeHasOwnProperty =
      js.Dynamic.global.Object.prototype.hasOwnProperty
        .asInstanceOf[js.ThisFunction1[js.Dictionary[_], String, scala.Boolean]]
  }

  @inline
  private def safeHasOwnProperty(dict: js.Dictionary[_], key: String): scala.Boolean =
    Cache.safeHasOwnProperty(dict, key)

  @js.native
  private trait DictionaryRawApply[A] extends js.Object {

    /** Reads a field of this object by its name.
     *
     *  This must not be called if the dictionary does not contain the key.
     */
    @JSBracketAccess
    def rawApply(key: String): A = js.native

    /** Writes a field of this object. */
    @JSBracketAccess
    def rawUpdate(key: String, value: A): Unit = js.native
  }

  def dictGetOrElse[A](dict: js.Dictionary[_ <: A], key: String, default: A): A = {
    if (dictContains(dict, key))
      dictRawApply(dict, key)
    else
      default
  }

  def dictGetOrElseAndRemove[A](dict: js.Dictionary[_ <: A], key: String, default: A): A = {
    if (dictContains(dict, key)) {
      val result = dictRawApply(dict, key)
      js.special.delete(dict, key)
      result
    } else {
      default
    }
  }

  @inline
  def dictRawApply[A](dict: js.Dictionary[A], key: String): A =
    dict.asInstanceOf[DictionaryRawApply[A]].rawApply(key)

  def dictContains[A](dict: js.Dictionary[A], key: String): scala.Boolean = {
    /* We have to use a safe version of hasOwnProperty, because
     * "hasOwnProperty" could be a key of this dictionary.
     */
    safeHasOwnProperty(dict, key)
  }

  @inline
  def dictSet[A](dict: js.Dictionary[A], key: String, value: A): Unit =
    dict.asInstanceOf[DictionaryRawApply[A]].rawUpdate(key, value)

  @js.native
  private trait MapRaw[K, V] extends js.Object {
    def has(key: K): scala.Boolean = js.native
    def get(key: K): js.UndefOr[V] = js.native
    def set(key: K, value: V): Unit = js.native
  }

  @inline
  def mapHas[K, V](map: js.Map[K, V], key: K): scala.Boolean =
    map.asInstanceOf[MapRaw[K, V]].has(key)

  @inline
  def mapGet[K, V](map: js.Map[K, V], key: K): js.UndefOr[V] =
    map.asInstanceOf[MapRaw[K, V]].get(key)

  @inline
  def mapSet[K, V](map: js.Map[K, V], key: K, value: V): Unit =
    map.asInstanceOf[MapRaw[K, V]].set(key, value)

  @inline
  def forArrayElems[A](array: js.Array[A])(f: js.Function1[A, Any]): Unit = {
    val len = array.length
    var i = 0
    while (i != len) {
      f(array(i))
      i += 1
    }
  }

  @inline def toUint(x: scala.Double): scala.Double =
    (x.asInstanceOf[js.Dynamic] >>> 0.asInstanceOf[js.Dynamic]).asInstanceOf[scala.Double]

  object Implicits {
    implicit def enableJSStringOps(x: String): js.JSStringOps =
      x.asInstanceOf[js.JSStringOps]

    implicit def enableJSNumberOps(x: Int): js.JSNumberOps =
      x.asInstanceOf[js.JSNumberOps]

    implicit def enableJSNumberOps(x: scala.Double): js.JSNumberOps =
      x.asInstanceOf[js.JSNumberOps]
  }

  object DynamicImplicits {
    @inline implicit def truthValue(x: js.Dynamic): scala.Boolean =
      (!(!x)).asInstanceOf[scala.Boolean]

    implicit def number2dynamic(x: scala.Double): js.Dynamic =
      x.asInstanceOf[js.Dynamic]

    implicit def boolean2dynamic(x: scala.Boolean): js.Dynamic =
      x.asInstanceOf[js.Dynamic]
  }
}
