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

import org.scalajs.linker.interface.unstable.ModuleInitializerImpl

import Fingerprint.FingerprintBuilder

/** A module initializer for a Scala.js application.
 *
 *  When linking a Scala.js application, a sequence of `ModuleInitializer`s can
 *  be given. Those module initializers will be executed at the startup of the
 *  application. More specifically, the top-level code of the ECMAScript 2015
 *  module emitted for the application will invoke the specified module
 *  initializers in the specified order, after having initialized everything
 *  else (notably static initializers).
 *
 *  Instances of `ModuleInitializer` can be created with methods of
 *  [[ModuleInitializer$ the ModuleInitializer companion object]].
 */
abstract class ModuleInitializer private[interface] () {
  private[interface] def impl: ModuleInitializerImpl
}

/** Factory for [[ModuleInitializer]]s. */
object ModuleInitializer {
  import ModuleInitializerImpl._

  /** Makes a [[ModuleInitializer]] that calls a static zero-argument method
   *  returning `Unit` in a top-level `class`.
   *
   *  @param className
   *    The fully-qualified name of the class, e.g., `"foo.bar.Babar"`.
   *  @param mainMethodName
   *    The name of the main method to invoke, e.g., `"main"`.
   */
  def mainMethod(className: String,
      mainMethodName: String): ModuleInitializer = {
    VoidMainMethod(className, mainMethodName)
  }

  /** Makes a [[ModuleInitializer]] that calls a static method of a top-level
   *  `class` taking an `Array[String]` and returning `Unit`.
   *
   *  An empty array is passed as argument.
   *
   *  @param className
   *    The fully-qualified name of the class, e.g., `"foo.bar.Babar"`.
   *  @param mainMethodName
   *    The name of the main method to invoke, e.g., `"main"`.
   */
  def mainMethodWithArgs(className: String,
      mainMethodName: String): ModuleInitializer = {
    mainMethodWithArgs(className, mainMethodName, Nil)
  }

  /** Makes a [[ModuleInitializer]] that calls a static method of a top-level
   *  `class` taking an `Array[String]` and returning `Unit`.
   *
   *  An array containing the specified `args` is passed as argument.
   *
   *  @param className
   *    The fully-qualified name of the class, e.g., `"foo.bar.Babar"`.
   *  @param mainMethodName
   *    The name of the main method to invoke, e.g., `"main"`.
   *  @param args
   *    The arguments to pass as an array.
   */
  def mainMethodWithArgs(className: String, mainMethodName: String,
      args: List[String]): ModuleInitializer = {
    MainMethodWithArgs(className, mainMethodName, args)
  }

  private implicit object ModuleInitializerFingerprint
      extends Fingerprint[ModuleInitializer] {

    override def fingerprint(moduleInitializer: ModuleInitializer): String =
      moduleInitializer.impl match {
        case VoidMainMethod(className, encodedMainMethodName) =>
          new FingerprintBuilder("VoidMainMethod")
            .addField("className", className)
            .addField("encodedMainMethodName", encodedMainMethodName)
            .build()

        case MainMethodWithArgs(className, encodedMainMethodName, args) =>
          new FingerprintBuilder("MainMethodWithArgs")
            .addField("className", className)
            .addField("encodedMainMethodName", encodedMainMethodName)
            .addField("args", args)
            .build()
      }
  }

  def fingerprint(moduleInitializer: ModuleInitializer): String =
    Fingerprint.fingerprint(moduleInitializer)
}
