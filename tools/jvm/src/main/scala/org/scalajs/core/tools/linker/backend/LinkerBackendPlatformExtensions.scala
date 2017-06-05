/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js tools             **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013-2017, LAMP/EPFL   **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */

package org.scalajs.core.tools.linker.backend

import org.scalajs.core.tools.sem.Semantics

import org.scalajs.core.tools.linker.backend.closure.ClosureLinkerBackend

trait LinkerBackendPlatformExtensions { this: LinkerBackend.type =>
  def apply(semantics: Semantics, outputMode: OutputMode,
      moduleKind: ModuleKind, config: Config): LinkerBackend = {

    if (config.closureCompiler) {
      require(outputMode == OutputMode.ECMAScript51Isolated,
          s"Cannot use output mode $outputMode with the Closure Compiler")
      new ClosureLinkerBackend(semantics, moduleKind, config)
    } else {
      new BasicLinkerBackend(semantics, outputMode, moduleKind, config)
    }
  }
}

object LinkerBackendPlatformExtensions {
  import LinkerBackend.Config

  final class ConfigExt(val config: Config) extends AnyVal {
    /** Whether to actually use the Google Closure Compiler pass. */
    def closureCompiler: Boolean = config.closureCompilerIfAvailable

    def withClosureCompiler(closureCompiler: Boolean): Config =
      config.withClosureCompilerIfAvailable(closureCompiler)
  }
}
