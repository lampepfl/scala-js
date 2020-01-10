package build

import com.typesafe.tools.mima.core._
import com.typesafe.tools.mima.core.ProblemFilters._

object BinaryIncompatibilities {
  val IR = Seq(
  )

  val Tools = Seq(
  )

  val JSEnvs = Seq(
  )

  val JSEnvsTestKit = Seq(
  )

  val SbtPlugin = Seq(
  )

  val TestCommon = Seq(
  )

  val TestAdapter = TestCommon ++ Seq(
  )

  val CLI = Seq(
  )

  val Library = Seq(
    exclude[ReversedMissingMethodProblem]("scala.scalajs.js.LowPrioAnyImplicits.wrapMap"),
    exclude[ReversedMissingMethodProblem]("scala.scalajs.js.LowPrioAnyImplicits.wrapSet")
  )

  val TestInterface = Seq(
  )
}
