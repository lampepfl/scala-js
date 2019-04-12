package org.scalajs.linker.test

import scala.concurrent._
import scala.concurrent.ExecutionContext.Implicits.global

import scala.scalajs.js
import scala.scalajs.js.annotation._
import scala.scalajs.js.JSConverters._

import java.net.URI

import org.scalajs.io._

import org.scalajs.logging._

import org.scalajs.linker._
import org.scalajs.linker.irio._

@JSExportTopLevel("TestSuiteLinker")
object QuickLinker {
  /** Link the Scala.js test suite on Node.js */
  @JSExport
  def linkTestSuiteNode(cp: js.Array[String], outputPath: String): js.Promise[Unit] = {
    val config = StandardLinker.Config()
      .withSemantics(build.TestSuiteLinkerOptions.semantics _)
      .withCheckIR(true)
      .withBatchMode(true)

    val linker = StandardLinker(config)

    val moduleInitializers = {
      build.TestSuiteLinkerOptions.moduleInitializers :+
      // Copied from org.scalajs.testing.adapter.TestAdapaterInitializer.
      ModuleInitializer.mainMethod("org.scalajs.testing.interface.Bridge", "start")
    }

    val smPath = outputPath + ".map"

    def relURI(path: String) =
      new URI(null, null, NodePath.basename(path), null)

    val out = LinkerOutput(WritableNodeVirtualBinaryFile(outputPath))
      .withSourceMap(WritableNodeVirtualBinaryFile(smPath))
      .withSourceMapURI(relURI(smPath))
      .withJSFileURI(relURI(outputPath))

    val cache = (new IRFileCache).newCache

    NodeScalaJSIRContainer.fromClasspath(cp.toSeq)
      .flatMap(cache.cached _)
      .flatMap(linker.link(_, moduleInitializers, out, new ScalaConsoleLogger))
      .toJSPromise
  }

  @JSImport("path", JSImport.Namespace)
  @js.native
  private object NodePath extends js.Object {
    def basename(str: String): String = js.native
  }
}
