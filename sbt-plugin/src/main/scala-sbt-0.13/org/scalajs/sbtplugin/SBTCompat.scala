package org.scalajs.sbtplugin

import sbt._

import org.scalajs.core.tools.io.FileVirtualFile

private[sbtplugin] object SBTCompat {
  type IncOptions = sbt.inc.IncOptions

  type CompileAnalysis = sbt.inc.Analysis

  class sbtUnchecked extends scala.annotation.Annotation

  val formatImplicits: sbt.Cache.type = sbt.Cache

  def moduleIDWithConfigurations(moduleID: ModuleID,
      configurations: Option[String]): ModuleID = {
    moduleID.copy(configurations = configurations)
  }

  def crossVersionAddScalaJSPart(cross: CrossVersion,
      part: String): CrossVersion = {
    cross match {
      case CrossVersion.Disabled =>
        CrossVersion.binaryMapped(_ => part)
      case cross: CrossVersion.Binary =>
        CrossVersion.binaryMapped(
            cross.remapVersion.andThen(part + "_" + _))
      case cross: CrossVersion.Full =>
        CrossVersion.fullMapped(
            cross.remapVersion.andThen(part + "_" + _))
    }
  }

  /** Patches the IncOptions so that .sjsir files are pruned as needed.
   *
   *  This complicated logic patches the ClassfileManager factory of the given
   *  IncOptions with one that is aware of .sjsir files emitted by the Scala.js
   *  compiler. This makes sure that, when a .class file must be deleted, the
   *  corresponding .sjsir file are also deleted.
   */
  def scalaJSPatchIncOptions(incOptions: IncOptions): IncOptions = {
    val inheritedNewClassfileManager = incOptions.newClassfileManager
    val newClassfileManager = () => new sbt.inc.ClassfileManager {
      private[this] val inherited = inheritedNewClassfileManager()

      def delete(classes: Iterable[File]): Unit = {
        inherited.delete(classes flatMap { classFile =>
          val scalaJSFiles = if (classFile.getPath endsWith ".class") {
            val f = FileVirtualFile.withExtension(classFile, ".class", ".sjsir")
            if (f.exists) List(f)
            else Nil
          } else Nil
          classFile :: scalaJSFiles
        })
      }

      def generated(classes: Iterable[File]): Unit = inherited.generated(classes)
      def complete(success: Boolean): Unit = inherited.complete(success)
    }
    incOptions.withNewClassfileManager(newClassfileManager)
  }
}
