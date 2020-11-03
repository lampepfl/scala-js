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

package org.scalajs.linker.interface

import Fingerprint.FingerprintBuilder

/** ECMAScript features to use when linking to JavaScript.
 *
 *  The options in `ESFeatures` specify what features of modern versions of
 *  JavaScript are used by the Scala.js linker.
 *
 *  - Options whose name is of the form `useX` *force* the linker to use the
 *    corresponding features, guaranteeing that the specific semantics that
 *    they provide will be used.
 *  - Options whose name is of the form `allowX` *allow* the linker to use the
 *    corresponding features if it supports them. Support for such options can
 *    be dropped in any subsequent version of the linker, including patch
 *    versions.
 */
final class ESFeatures private (
    /** Whether to use ECMAScript 2015 features, such as classes and arrow
     *  functions.
     */
    val useECMAScript2015: Boolean,
    /** EXPERIMENTAL: Whether to allow using ECMAScript `BigInt`s to implement
     *  `Long`s.
     */
    val allowBigIntsForLongs: Boolean
) {
  import ESFeatures._

  private def this() = {
    this(
        useECMAScript2015 = true,
        allowBigIntsForLongs = false
    )
  }

  def withUseECMAScript2015(useECMAScript2015: Boolean): ESFeatures =
    copy(useECMAScript2015 = useECMAScript2015)

  def withAllowBigIntsForLongs(allowBigIntsForLongs: Boolean): ESFeatures =
    copy(allowBigIntsForLongs = allowBigIntsForLongs)

  override def equals(that: Any): Boolean = that match {
    case that: ESFeatures =>
      this.useECMAScript2015 == that.useECMAScript2015 &&
        this.allowBigIntsForLongs == that.allowBigIntsForLongs
    case _ =>
      false
  }

  override def hashCode(): Int = {
    import scala.util.hashing.MurmurHash3._
    var acc = HashSeed
    acc = mix(acc, useECMAScript2015.##)
    acc = mixLast(acc, allowBigIntsForLongs.##)
    finalizeHash(acc, 2)
  }

  override def toString(): String = {
    s"""ESFeatures(
       |  useECMAScript2015 = $useECMAScript2015,
       |  allowBigIntsForLongs = $allowBigIntsForLongs
       |)""".stripMargin
  }

  private def copy(
      useECMAScript2015: Boolean = this.useECMAScript2015,
      allowBigIntsForLongs: Boolean = this.allowBigIntsForLongs
  ): ESFeatures = {
    new ESFeatures(
        useECMAScript2015 = useECMAScript2015,
        allowBigIntsForLongs = allowBigIntsForLongs
    )
  }
}

object ESFeatures {
  private val HashSeed =
    scala.util.hashing.MurmurHash3.stringHash(classOf[ESFeatures].getName)

  /** Default configuration of ECMAScript features.
   *
   *  - `useECMAScript2015`: true
   *  - `allowBigIntsForLongs`: false
   */
  val Defaults: ESFeatures = new ESFeatures()

  private[interface] implicit object ESFeaturesFingerprint extends Fingerprint[ESFeatures] {

    override def fingerprint(esFeatures: ESFeatures): String = {
      new FingerprintBuilder("ESFeatures")
        .addField("useECMAScript2015", esFeatures.useECMAScript2015)
        .addField("allowBigIntsForLongs", esFeatures.allowBigIntsForLongs)
        .build()
    }
  }
}
