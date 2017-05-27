/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js tools             **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013-2015, LAMP/EPFL   **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package org.scalajs.core.tools.linker.frontend

import org.scalajs.core.tools.logging.Logger
import org.scalajs.core.tools.io.VirtualScalaJSIRFile

import org.scalajs.core.tools.sem.Semantics
import org.scalajs.core.tools.javascript.ESLevel

import org.scalajs.core.tools.linker._
import org.scalajs.core.tools.linker.analyzer.SymbolRequirement
import org.scalajs.core.tools.linker.frontend.optimizer.{GenIncOptimizer, IncOptimizer}

/** The frontend of the Scala.js linker. Produces a [[LinkingUnit]]
 *
 *  You probably want to use an instance of [[linker.Linker]], rather than this
 *  low-level class.
 *
 *  Attention: [[LinkerFrontend]] does not cache the IR input. It is advisable to do
 *  so, unless all IR is already in memory.
 */
final class LinkerFrontend private[frontend] (
    val semantics: Semantics,
    val esLevel: ESLevel,
    config: LinkerFrontend.Config,
    optimizerFactory: Option[GenIncOptimizer.OptimizerFactory]) {

  @deprecated(
      "The withSourceMap parameter is ignored. " +
      "Use LinkerFrontend.apply().",
      "0.6.17")
  def this(semantics: Semantics, esLevel: ESLevel, withSourceMap: Boolean,
      config: LinkerFrontend.Config,
      optimizerFactory: Option[GenIncOptimizer.OptimizerFactory]) = {
    this(semantics, esLevel, config, optimizerFactory)
  }

  @deprecated("withSourceMap is always true", "0.6.17")
  val withSourceMap: Boolean = true

  private[this] val linker: BaseLinker =
    new BaseLinker(semantics, esLevel)

  private[this] val optOptimizer: Option[GenIncOptimizer] =
    optimizerFactory.map(_(semantics, esLevel, true))

  private[this] val refiner: Refiner = new Refiner

  /** Link and optionally optimize the given IR to a [[LinkingUnit]]. */
  @deprecated("Use the overload with explicit module initializers.", "0.6.15")
  def link(irFiles: Seq[VirtualScalaJSIRFile],
      symbolRequirements: SymbolRequirement, logger: Logger): LinkingUnit = {
    link(irFiles, Nil, symbolRequirements, logger)
  }

  /** Link and optionally optimize the given IR to a [[LinkingUnit]]. */
  def link(irFiles: Seq[VirtualScalaJSIRFile],
      moduleInitializers: Seq[ModuleInitializer],
      symbolRequirements: SymbolRequirement, logger: Logger): LinkingUnit = {

    val preOptimizerRequirements = optOptimizer.fold(symbolRequirements) {
      optimizer => symbolRequirements ++ optimizer.symbolRequirements
    }

    val linkResult = logger.time("Basic Linking") {
      linker.linkInternal(irFiles, moduleInitializers, logger,
          preOptimizerRequirements, config.bypassLinkingErrors, config.checkIR)
    }

    optOptimizer.fold(linkResult) { optimizer =>
      if (linkResult.isComplete) {
        optimize(linkResult, symbolRequirements, optimizer, logger)
      } else {
        logger.warn("Not running the optimizer because there were linking errors.")
        linkResult
      }
    }
  }

  private def optimize(unit: LinkingUnit, symbolRequirements: SymbolRequirement,
      optimizer: GenIncOptimizer, logger: Logger): LinkingUnit = {
    val optimized = logger.time("Inc. optimizer") {
      optimizer.update(unit, logger)
    }

    logger.time("Refiner") {
      refiner.refine(optimized, symbolRequirements, logger)
    }
  }
}

object LinkerFrontend extends LinkerFrontendPlatformExtensions {
  /** Configurations relevant to the frontend */
  final class Config private (
      /** Whether to only warn if the linker has errors. */
      val bypassLinkingErrors: Boolean = false,
      /** If true, performs expensive checks of the IR for the used parts. */
      val checkIR: Boolean = false,
      /** Whether to use the Scala.js optimizer. */
      val optimizer: Boolean = true,
      /** Whether things that can be parallelized should be parallelized.
       *  On the JavaScript platform, this does not have any effect.
       */
      val parallel: Boolean = true
  ) {
    @deprecated(
        "Bypassing linking errors will not be possible in the next major version.",
        "0.6.6")
    def withBypassLinkingErrors(bypassLinkingErrors: Boolean): Config =
      copy(bypassLinkingErrors = bypassLinkingErrors)

    // Non-deprecated version to call from the sbt plugin
    private[scalajs] def withBypassLinkingErrorsInternal(
        bypassLinkingErrors: Boolean): Config = {
      copy(bypassLinkingErrors = bypassLinkingErrors)
    }

    def withCheckIR(checkIR: Boolean): Config =
      copy(checkIR = checkIR)

    def withOptimizer(optimizer: Boolean): Config =
      copy(optimizer = optimizer)

    def withParallel(parallel: Boolean): Config =
      copy(parallel = parallel)

    private def copy(
        bypassLinkingErrors: Boolean = bypassLinkingErrors,
        checkIR: Boolean = checkIR,
        optimizer: Boolean = optimizer,
        parallel: Boolean = parallel): Config = {
      new Config(bypassLinkingErrors, checkIR, optimizer, parallel)
    }
  }

  object Config {
    def apply(): Config = new Config()
  }
}
