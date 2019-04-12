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

package org.scalajs.jsenv.nodejs


import scala.annotation.tailrec

import java.io._
import java.nio.charset.StandardCharsets
import java.nio.file._

import org.scalajs.jsenv._

import org.scalajs.io.JSUtils.escapeJS
import org.scalajs.logging._

import com.google.common.jimfs.Jimfs

final class NodeJSEnv(config: NodeJSEnv.Config) extends JSEnv {
  import NodeJSEnv._

  def this() = this(NodeJSEnv.Config())

  val name: String = "Node.js"

  def start(input: Input, runConfig: RunConfig): JSRun = {
    NodeJSEnv.validator.validate(runConfig)
    validateInput(input)
    internalStart(initFiles, input, runConfig)
  }

  def startWithCom(input: Input, runConfig: RunConfig,
      onMessage: String => Unit): JSComRun = {
    NodeJSEnv.validator.validate(runConfig)
    validateInput(input)
    ComRun.start(runConfig, onMessage) { comLoader =>
      internalStart(initFiles :+ comLoader, input, runConfig)
    }
  }

  private def validateInput(input: Input): Unit = {
    input match {
      case _:Input.ScriptsToLoad | _:Input.ESModulesToLoad |
          _:Input.CommonJSModulesToLoad =>
        // ok
      case _ =>
        throw new UnsupportedInputException(input)
    }
  }

  private def internalStart(initFiles: List[Path], input: Input, runConfig: RunConfig): JSRun = {
    val command = config.executable :: config.args
    val externalConfig = ExternalJSRun.Config()
      .withEnv(env)
      .withRunConfig(runConfig)
    ExternalJSRun.start(command, externalConfig)(
        NodeJSEnv.write(initFiles, input))
  }

  private def initFiles: List[Path] = config.sourceMap match {
    case SourceMap.Disable           => Nil
    case SourceMap.EnableIfAvailable => installSourceMapIfAvailable :: Nil
    case SourceMap.Enable            => installSourceMap :: Nil
  }

  private def inputFiles(input: Input) = input match {
    case Input.ScriptsToLoad(scripts) => scripts
    case _                            => throw new UnsupportedInputException(input)
  }

  private def env: Map[String, String] =
    Map("NODE_MODULE_CONTEXTS" -> "0") ++ config.env
}

object NodeJSEnv {
  private lazy val fs = Jimfs.newFileSystem()

  private lazy val validator = ExternalJSRun.supports(RunConfig.Validator())

  private lazy val installSourceMapIfAvailable = {
    Files.write(
        fs.getPath("optionalSourceMapSupport.js"),
        """
          |try {
          |  require('source-map-support').install();
          |} catch (e) {
          |};
        """.stripMargin.getBytes(StandardCharsets.UTF_8))
  }

  private lazy val installSourceMap = {
    Files.write(
        fs.getPath("sourceMapSupport.js"),
        "require('source-map-support').install();".getBytes(StandardCharsets.UTF_8))
  }

  private def write(initFiles: List[Path], input: Input)(out: OutputStream): Unit = {
    val p = new PrintStream(out, false, "UTF8")
    try {
      def writeRunScript(path: Path): Unit = {
        try {
          val f = path.toFile
          val pathJS = "\"" + escapeJS(f.getAbsolutePath) + "\""
          p.println(s"""
            require('vm').runInThisContext(
              require('fs').readFileSync($pathJS, { encoding: "utf-8" }),
              { filename: $pathJS, displayErrors: true }
            );
          """)
        } catch {
          case _: UnsupportedOperationException =>
            val code = new String(Files.readAllBytes(path), StandardCharsets.UTF_8)
            val codeJS = "\"" + escapeJS(code) + "\""
            val pathJS = "\"" + escapeJS(path.toString) + "\""
            p.println(s"""
              require('vm').runInThisContext(
                $codeJS,
                { filename: $pathJS, displayErrors: true }
              );
            """)
        }
      }

      for (initFile <- initFiles)
        writeRunScript(initFile)

      input match {
        case Input.ScriptsToLoad(scripts) =>
          for (script <- scripts)
            writeRunScript(script)

        case Input.CommonJSModulesToLoad(modules) =>
          for (module <- modules)
            p.println(s"""require("${escapeJS(toFile(module).getAbsolutePath)}")""")

        case Input.ESModulesToLoad(modules) =>
          if (modules.nonEmpty) {
            val uris = modules.map(m => toFile(m).toURI)

            val imports = uris.map { uri =>
              s"""import("${escapeJS(uri.toASCIIString)}")"""
            }
            val importChain = imports.reduceLeft { (prev, imprt) =>
              s"""$prev.then(_ => $imprt)"""
            }

            val importerFileContent = {
              s"""
                |$importChain.catch(e => {
                |  console.error(e);
                |  process.exit(1);
                |});
              """.stripMargin
            }
            val f = createTmpFile("importer.js")
            Files.write(f.toPath, importerFileContent.getBytes(StandardCharsets.UTF_8))
            p.println(s"""require("${escapeJS(f.getAbsolutePath)}");""")
          }
      }
    } finally {
      p.close()
    }
  }

  private def toFile(path: Path): File = {
    try {
      path.toFile
    } catch {
      case _: UnsupportedOperationException =>
        val f = createTmpFile(path.toString)
        Files.copy(path, f.toPath(), StandardCopyOption.REPLACE_EXISTING)
        f
    }
  }

  // tmpSuffixRE and createTmpFile copied from HTMLRunnerBuilder.scala

  private val tmpSuffixRE = """[a-zA-Z0-9-_.]*$""".r

  private def createTmpFile(path: String): File = {
    /* - createTempFile requires a prefix of at least 3 chars
     * - we use a safe part of the path as suffix so the extension stays (some
     *   browsers need that) and there is a clue which file it came from.
     */
    val suffix = tmpSuffixRE.findFirstIn(path).orNull

    val f = File.createTempFile("tmp-", suffix)
    f.deleteOnExit()
    f
  }

  /** Requirements for source map support. */
  sealed abstract class SourceMap

  object SourceMap {
    /** Disable source maps. */
    case object Disable extends SourceMap

    /** Enable source maps if `source-map-support` is available. */
    case object EnableIfAvailable extends SourceMap

    /** Always enable source maps.
     *
     *  If `source-map-support` is not available, loading the .js code will
     *  fail.
     */
    case object Enable extends SourceMap
  }

  final class Config private (
      val executable: String,
      val args: List[String],
      val env: Map[String, String],
      val sourceMap: SourceMap
  ) {
    private def this() = {
      this(
          executable = "node",
          args = Nil,
          env = Map.empty,
          sourceMap = SourceMap.EnableIfAvailable
      )
    }

    def withExecutable(executable: String): Config =
      copy(executable = executable)

    def withArgs(args: List[String]): Config =
      copy(args = args)

    def withEnv(env: Map[String, String]): Config =
      copy(env = env)

    def withSourceMap(sourceMap: SourceMap): Config =
      copy(sourceMap = sourceMap)

    /** Forces enabling (true) or disabling (false) source maps.
     *
     *  `sourceMap = true` maps to [[SourceMap.Enable]]. `sourceMap = false`
     *  maps to [[SourceMap.Disable]]. [[SourceMap.EnableIfAvailable]] is never
     *  used by this method.
     */
    def withSourceMap(sourceMap: Boolean): Config =
      withSourceMap(if (sourceMap) SourceMap.Enable else SourceMap.Disable)

    private def copy(
        executable: String = executable,
        args: List[String] = args,
        env: Map[String, String] = env,
        sourceMap: SourceMap = sourceMap
    ): Config = {
      new Config(executable, args, env, sourceMap)
    }
  }

  object Config {
    /** Returns a default configuration for a [[NodeJSEnv]].
     *
     *  The defaults are:
     *
     *  - `executable`: `"node"`
     *  - `args`: `Nil`
     *  - `env`: `Map.empty`
     *  - `sourceMap`: [[SourceMap.EnableIfAvailable]]
     */
    def apply(): Config = new Config()
  }
}
