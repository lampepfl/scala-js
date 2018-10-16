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

package org.scalajs.ir

object ScalaJSVersions {

  /* DO NOT MAKE THESE 'final val's!
   * When referring to these "constants" from separate libraries, if it is a
   * 'final val', the value will be copied in the binaries of those libraries.
   * If they are then linked to a different version of the IR artifact, their
   * copy of these constants will not be updated.
   */

  /** Scala.js version. */
  val current: String = "1.0.0-SNAPSHOT"

  /** true iff the Scala.js version is a snapshot version. */
  val currentIsSnapshot: Boolean = current endsWith "-SNAPSHOT"

  /** Version of binary IR emitted by this version of Scala.js.
   *
   *  This should be either of:
   *  - a prior release version (i.e. "0.5.0", *not* "0.5.0-SNAPSHOT")
   *  - `current`
   */
  val binaryEmitted: String = current

  /** Versions whose binary files we can support (used by deserializer) */
  val binarySupported: Set[String] = {
    Set(binaryEmitted)
  }

  // Just to be extra safe
  assert(binarySupported contains binaryEmitted)

}
