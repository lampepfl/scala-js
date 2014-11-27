/* Scala.js compiler
 * Copyright 2013 LAMP/EPFL
 * @author  Sébastien Doeraene
 */

package scala.scalajs.compiler

import scala.tools.nsc._

/** Hacks to have our source code compatible with 2.10 and 2.11.
 *  It exposes 2.11 API in a 2.10 compiler.
 *
 *  @author Sébastien Doeraene
 */
trait Compat210Component {

  val global: Global

  import global._

  // unexpandedName replaces originalName

  implicit final class SymbolCompat(self: Symbol) {
    def unexpandedName: Name = self.originalName
    def originalName: Name = sys.error("infinite loop in Compat")

    def isLocalToBlock: Boolean = self.isLocal
  }

  // enteringPhase/exitingPhase replace beforePhase/afterPhase

  @inline final def enteringPhase[T](ph: Phase)(op: => T): T = {
    global.enteringPhase(ph)(op)
  }

  @inline final def exitingPhase[T](ph: Phase)(op: => T): T = {
    global.exitingPhase(ph)(op)
  }

  private implicit final class GlobalCompat(
      self: Compat210Component.this.global.type) {

    def enteringPhase[T](ph: Phase)(op: => T): T = self.beforePhase(ph)(op)
    def beforePhase[T](ph: Phase)(op: => T): T = sys.error("infinite loop in Compat")

    def exitingPhase[T](ph: Phase)(op: => T): T = self.afterPhase(ph)(op)
    def afterPhase[T](ph: Phase)(op: => T): T = sys.error("infinite loop in Compat")
  }

  // ErasedValueType has a different encoding

  implicit final class ErasedValueTypeCompat(self: global.ErasedValueType) {
    def valueClazz: Symbol = self.original.typeSymbol
    def erasedUnderlying: Type =
      enteringPhase(currentRun.erasurePhase)(
          erasure.erasedValueClassArg(self.original))
    def original: TypeRef = sys.error("infinite loop in Compat")
  }

  // repeatedToSingle

  @inline final def repeatedToSingle(t: Type) =
    global.definitions.repeatedToSingle(t)

  private implicit final class DefinitionsCompat(
    self: Compat210Component.this.global.definitions.type) {

    def repeatedToSingle(t: Type) = t match {
      case TypeRef(_, self.RepeatedParamClass, arg :: Nil) => arg
      case _ => t
    }

  }

  // run.runDefinitions bundles methods and state related to the run
  // that were previously in definitions itself

  implicit final class RunCompat(self: Run) {
    val runDefinitions: Compat210Component.this.global.definitions.type =
      global.definitions
  }

  // Mode.FUNmode replaces analyzer.FUNmode

  object Mode {
    import Compat210Component.AnalyzerCompat
    // No type ascription! Type is different in 2.10 / 2.11
    val FUNmode = analyzer.FUNmode
  }

  /* Constants and predicates for primitives were moved to the ScalaPrimitives
   * companion object. This only makes a 'val ScalaPrimitives' available which
   * is either the true ScalaPrimitives companion if it exists, or an empty
   * object. Typically the 2 following imports will be necessary together:
   *
   *   import scalaPrimitives._
   *   import ScalaPrimitives._
   */

  val ScalaPrimitives = Compat210Component.ScalaPrimitivesCompat
}

object Compat210Component {
  private object LowPriorityMode {
    object Mode {
      def FUNmode = sys.error("infinite loop in Compat")
    }
  }

  private implicit final class AnalyzerCompat(self: scala.tools.nsc.typechecker.Analyzer) {
    def FUNmode = {
      import Compat210Component.LowPriorityMode._
      {
        import scala.reflect.internal._
        Mode.FUNmode
      }
    }
  }

  object LowPriorityScalaPrimitives {
    object ScalaPrimitives
  }

  val ScalaPrimitivesCompat = {
    import LowPriorityScalaPrimitives._
    {
      import scala.tools.nsc.backend._
      ScalaPrimitives
    }
  }
}
