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

package org.scalajs.sbtplugin

import scala.language.reflectiveCalls

import scala.annotation.tailrec

// Import Future explicitly to avoid collision with sbt.Future.
import scala.concurrent.{Future, _}
import scala.concurrent.duration._

import scala.util.{Failure, Success}

import java.util.concurrent.atomic.AtomicReference

import sbt._
import sbt.Keys._
import sbt.complete.DefaultParsers._

import org.portablescala.sbtplatformdeps.PlatformDepsPlugin.autoImport._

import org.scalajs.linker.interface._
import org.scalajs.linker.interface.unstable.IRFileImpl

import org.scalajs.jsenv._

import org.scalajs.testing.adapter.{TestAdapter, HTMLRunnerBuilder, TestAdapterInitializer}

import Loggers._

import sjsonnew.BasicJsonProtocol._

/** Implementation details of `ScalaJSPlugin`. */
private[sbtplugin] object ScalaJSPluginInternal {

  import ScalaJSPlugin.autoImport.{ModuleKind => _, _}

  @tailrec
  final private def registerResource[T <: AnyRef](
      l: AtomicReference[List[T]], r: T): r.type = {
    val prev = l.get()
    if (l.compareAndSet(prev, r :: prev)) r
    else registerResource(l, r)
  }

  private val allocatedIRCaches =
    new AtomicReference[List[IRFileCache.Cache]](Nil)

  private[sbtplugin] def freeAllIRCaches(): Unit =
    allocatedIRCaches.getAndSet(Nil).foreach(_.free())

  private val createdTestAdapters =
    new AtomicReference[List[TestAdapter]](Nil)

  private def newTestAdapter(jsEnv: JSEnv, input: Seq[Input],
      config: TestAdapter.Config): TestAdapter = {
    registerResource(createdTestAdapters, new TestAdapter(jsEnv, input, config))
  }

  private[sbtplugin] def closeAllTestAdapters(): Unit =
    createdTestAdapters.getAndSet(Nil).foreach(_.close())

  private def enhanceIRVersionNotSupportedException[A](body: => A): A = {
    object IRVersionNotSupportedException {
      def unapply(e: java.io.IOException): Option[String] = {
        if (e.getClass().getName() == "org.scalajs.ir.IRVersionNotSupportedException") {
          Some((e.asInstanceOf[{ def version: String }].version))
        } else {
          None
        }
      }
    }

    try {
      body
    } catch {
      case e @ IRVersionNotSupportedException(version) =>
        throw new java.io.IOException(
            s"${e.getMessage}\nYou may need to upgrade the Scala.js sbt " +
            s"plugin to version $version or later.",
            e)
    }
  }

  private def await[T](log: Logger)(body: ExecutionContext => Future[T]): T = {
    val ec = ExecutionContext.fromExecutor(
        ExecutionContext.global, t => log.trace(t))

    Await.result(body(ec), Duration.Inf)
  }

  private val scalajspParser = {
    loadForParser(scalaJSClassNamesOnClasspath) { (_, names) =>
      val examples = sbt.complete.FixedSetExamples(names.getOrElse(Nil))
      OptSpace ~> StringBasic.examples(examples)
    }
  }

  /** Patches the IncOptions so that .sjsir files are pruned, backed up and
   *  restored as needed.
   */
  def scalaJSPatchIncOptions(incOptions: IncOptions): IncOptions = {
    val sjsirFileManager = new SJSIRFileManager
    val newExternalHooks =
      incOptions.externalHooks.withExternalClassFileManager(sjsirFileManager)
    incOptions.withExternalHooks(newExternalHooks)
  }

  /** Settings for the production key (e.g. fastOptJS) of a given stage */
  private def scalaJSStageSettings(stage: Stage,
      key: TaskKey[Attributed[File]]): Seq[Setting[_]] = Seq(

      scalaJSLinkerBox in key := new CacheBox,

      scalaJSLinker in key := {
        val config = (scalaJSLinkerConfig in key).value
        val box = (scalaJSLinkerBox in key).value
        val linkerImpl = (scalaJSLinkerImpl in key).value
        val projectID = thisProject.value.id
        val configName = configuration.value.name
        val log = streams.value.log

        if (config.moduleKind != scalaJSLinkerConfig.value.moduleKind) {
          val keyName = key.key.label
          log.warn(
              "The module kind in " +
              s"`$projectID / $configName / $keyName / scalaJSLinkerConfig` " +
              "is different than the one in " +
              s"`$projectID / $configName / scalaJSLinkerConfig`. " +
              "Some things will go wrong.")
        }

        box.ensure(linkerImpl.clearableLinker(config))
      },

      // Have `clean` reset the state of the incremental linker
      clean in (This, Zero, This) := {
        val _ = (clean in (This, Zero, This)).value
        (scalaJSLinkerBox in key).value.foreach(_.clear())
        ()
      },

      usesScalaJSLinkerTag in key := {
        val projectPart = thisProject.value.id
        val configPart = configuration.value.name

        val stagePart = stage match {
          case Stage.FastOpt => "fastopt"
          case Stage.FullOpt => "fullopt"
        }

        Tags.Tag(s"uses-scalajs-linker-$projectPart-$configPart-$stagePart")
      },

      // Prevent this linker from being used concurrently
      concurrentRestrictions in Global +=
        Tags.limit((usesScalaJSLinkerTag in key).value, 1),

      scalaJSModuleInitializersFingerprints in key :=
        scalaJSModuleInitializers.value.map(ModuleInitializer.fingerprint),

      scalaJSLinkerConfigFingerprint in key :=
        StandardConfig.fingerprint((scalaJSLinkerConfig in key).value),

      key := Def.taskDyn {
        /* It is very important that we evaluate all of those `.value`s from
         * here, and not from within the `Def.task { ... }`, otherwise the
         * relevant dependencies will not show up in `inspect tree`. We use a
         * `Def.taskDyn` only to be able to tag the inner task with a tag that
         * is setting-dependent. But otherwise, the task does not have actually
         * dynamic dependencies, so `inspect tree` is happy with it.
         */
        val s = streams.value
        val irInfo = (scalaJSIR in key).value
        val moduleInitializers = scalaJSModuleInitializers.value
        val output = (artifactPath in key).value
        val linker = (scalaJSLinker in key).value
        val linkerImpl = (scalaJSLinkerImpl in key).value
        val usesLinkerTag = (usesScalaJSLinkerTag in key).value
        val sourceMapFile = new File(output.getPath + ".map")

        Def.task {
          val log = s.log
          val realFiles = irInfo.get(scalaJSSourceFiles).get
          val ir = irInfo.data

          def moduleInitializersChanged = (scalaJSModuleInitializersFingerprints in key)
            .previous
            .exists(_ != (scalaJSModuleInitializersFingerprints in key).value)

          def linkerConfigChanged = (scalaJSLinkerConfigFingerprint in key)
            .previous
            .exists(_ != (scalaJSLinkerConfigFingerprint in key).value)

          val configChanged = moduleInitializersChanged || linkerConfigChanged
          if (configChanged && output.exists()) {
            output.delete() // triggers re-linking through FileFunction.cached
          }

          FileFunction.cached(s.cacheDirectory, FilesInfo.lastModified,
              FilesInfo.exists) { _ => // We don't need the files

            val stageName = stage match {
              case Stage.FastOpt => "Fast"
              case Stage.FullOpt => "Full"
            }

            log.info(s"$stageName optimizing $output")

            IO.createDirectory(output.getParentFile)

            def relURI(path: String) = new URI(null, null, path, null)

            val out = LinkerOutput(linkerImpl.outputFile(output.toPath))
              .withSourceMap(linkerImpl.outputFile(sourceMapFile.toPath))
              .withSourceMapURI(relURI(sourceMapFile.getName))
              .withJSFileURI(relURI(output.getName))

            try {
              enhanceIRVersionNotSupportedException {
                val tlog = sbtLogger2ToolsLogger(log)
                await(log)(linker.link(ir, moduleInitializers, out, tlog)(_))
              }
            } catch {
              case e: LinkingException =>
                throw new MessageOnlyException(e.getMessage)
            }

            Set(output, sourceMapFile)
          } (realFiles.toSet)

          Attributed.blank(output).put(scalaJSSourceMap, sourceMapFile)
        }.tag(usesLinkerTag, ScalaJSTags.Link)
      }.value
  )

  val scalaJSConfigSettings: Seq[Setting[_]] = Seq(
      incOptions ~= scalaJSPatchIncOptions
  ) ++ (
      scalaJSStageSettings(Stage.FastOpt, fastOptJS) ++
      scalaJSStageSettings(Stage.FullOpt, fullOptJS)
  ) ++ (
      Seq(fastOptJS, fullOptJS).map { key =>
        moduleName in key := {
          val configSuffix = configuration.value match {
            case Compile => ""
            case config  => "-" + config.name
          }
          moduleName.value + configSuffix
        }
      }
  ) ++ Seq(
      // Note: this cache is not cleared by the sbt's clean task.
      scalaJSIRCacheBox := new CacheBox,

      scalaJSIR := {
        val linkerImpl = (scalaJSLinkerImpl in scalaJSIR).value

        val globalIRCache = scalaJSGlobalIRCacheBox.value
          .ensure(linkerImpl.irFileCache())

        val cache = scalaJSIRCacheBox.value
          .ensure(registerResource(allocatedIRCaches, globalIRCache.newCache))

        val classpath = Attributed.data(fullClasspath.value)
        val log = streams.value.log
        val tlog = sbtLogger2ToolsLogger(log)

        val (irFiles, paths) = enhanceIRVersionNotSupportedException {
          tlog.time("Update IR cache") {
            await(log) { eci =>
              implicit val ec = eci
              for {
                (irContainers, paths) <- linkerImpl.irContainers(classpath.map(_.toPath))
                irFiles <- cache.cached(irContainers)
              } yield (irFiles, paths)
            }
          }
        }

        Attributed
          .blank[Seq[IRFile]](irFiles)
          .put(scalaJSSourceFiles, paths.map(_.toFile))
      },

      scalaJSClassNamesOnClasspath := Def.task {
        val linkerImpl = scalaJSLinkerImpl.value

        await(streams.value.log) { eci =>
          implicit val ec = eci
          Future.traverse(scalaJSIR.value.data) { irFile =>
            linkerImpl.irFileClassName(irFile)
              .map(Some(_))
              .fallbackTo(Future.successful(None))
          }
        }.flatten
      }.storeAs(scalaJSClassNamesOnClasspath).triggeredBy(scalaJSIR).value,

      scalajsp := {
        val name = scalajspParser.parsed
        val linkerImpl = scalaJSLinkerImpl.value

        enhanceIRVersionNotSupportedException {
          val log = streams.value.log
          val prettyPrintedTree = await(log) { eci =>
            implicit val ec = eci
            Future.traverse(scalaJSIR.value.data) { irFile =>
              linkerImpl.irFileClassName(irFile).map { className =>
                if (className == name) Success(Some(irFile))
                else Success(None)
              }.recover { case t => Failure(t) }
            }.flatMap { irs =>
              irs.collectFirst {
                case Success(Some(f)) => linkerImpl.prettyPrintIRFile(f)
              }.getOrElse {
                val t = new MessageOnlyException(s"class $name not found on classpath")
                irs.collect { case Failure(st) => t.addSuppressed(st) }
                throw t
              }
            }
          }

          System.out.println(prettyPrintedTree)
        }
      },

      artifactPath in fastOptJS :=
        ((crossTarget in fastOptJS).value /
            ((moduleName in fastOptJS).value + "-fastopt.js")),

      artifactPath in fullOptJS :=
        ((crossTarget in fullOptJS).value /
            ((moduleName in fullOptJS).value + "-opt.js")),

      scalaJSLinkerConfig in fullOptJS ~= { prevConfig =>
        val useClosure = prevConfig.moduleKind != ModuleKind.ESModule
        prevConfig
          .withSemantics(_.optimized)
          .withClosureCompiler(useClosure)
          .withCheckIR(true)  // for safety, fullOpt is slow anyways.
      },

      scalaJSLinkedFile := Def.settingDyn {
        scalaJSStage.value match {
          case Stage.FastOpt => fastOptJS
          case Stage.FullOpt => fullOptJS
        }
      }.value,

      console := console.dependsOn(Def.task {
        streams.value.log.warn("Scala REPL doesn't work with Scala.js. You " +
            "are running a JVM REPL. JavaScript things won't work.")
      }).value,

      /* Do not inherit jsEnvInput from the parent configuration.
       * Instead, always derive it straight from the Zero configuration scope.
       */
      jsEnvInput := (jsEnvInput in (This, Zero, This)).value,

      // Add the Scala.js linked file to the Input for the JSEnv.
      jsEnvInput += {
        val linkedFile = scalaJSLinkedFile.value.data.toPath

        scalaJSLinkerConfig.value.moduleKind match {
          case ModuleKind.NoModule       => Input.Script(linkedFile)
          case ModuleKind.ESModule       => Input.ESModule(linkedFile)
          case ModuleKind.CommonJSModule => Input.CommonJSModule(linkedFile)
        }
      },

      scalaJSMainModuleInitializer := {
        mainClass.value.map { mainCl =>
          ModuleInitializer.mainMethodWithArgs(mainCl, "main")
        }
      },

      /* Do not inherit scalaJSModuleInitializers from the parent configuration.
       * Instead, always derive them straight from the Zero configuration
       * scope.
       */
      scalaJSModuleInitializers :=
        (scalaJSModuleInitializers in (This, Zero, This)).value,

      scalaJSModuleInitializers ++= {
        val mainClasses = discoveredMainClasses.value
        if (scalaJSUseMainModuleInitializer.value) {
          Seq(scalaJSMainModuleInitializer.value.getOrElse {
            if (mainClasses.isEmpty) {
              throw new MessageOnlyException(
                  "No main module initializer was specified, but " +
                  "scalaJSUseMainModuleInitializer was set to true. " +
                  "You can explicitly specify it either with " +
                  "`mainClass := Some(...)` or with " +
                  "`scalaJSMainModuleInitializer := Some(...)`")
            } else {
              throw new MessageOnlyException(
                  s"Multiple main classes (${mainClasses.mkString(", ")}) " +
                  "were found. " +
                  "You can explicitly specify the one you want with " +
                  "`mainClass := Some(...)` or with " +
                  "`scalaJSMainModuleInitializer := Some(...)`")
            }
          })
        } else {
          Seq.empty
        }
      },

      run := {
        if (!scalaJSUseMainModuleInitializer.value) {
          throw new MessageOnlyException("`run` is only supported with " +
              "scalaJSUseMainModuleInitializer := true")
        }

        val log = streams.value.log
        val env = jsEnv.value

        val className = mainClass.value.getOrElse("<unknown class>")
        log.info(s"Running $className. Hit any key to interrupt.")
        log.debug(s"with JSEnv ${env.name}")

        val input = jsEnvInput.value
        val config = RunConfig().withLogger(sbtLogger2ToolsLogger(log))

        Run.runInterruptible(env, input, config)
      },

      runMain := {
        throw new MessageOnlyException("`runMain` is not supported in Scala.js")
      }
  )

  val scalaJSCompileSettings: Seq[Setting[_]] = (
      scalaJSConfigSettings
  )

  val scalaJSTestSettings: Seq[Setting[_]] = (
      scalaJSConfigSettings
  ) ++ Seq(
      /* Always default to false for scalaJSUseMainModuleInitializer in testing
       * configurations, even if it is true in the Global configuration scope.
       */
      scalaJSUseMainModuleInitializer := false,

      // Use test module initializer by default.
      scalaJSUseTestModuleInitializer := true,

      scalaJSModuleInitializers ++= {
        val useMain = scalaJSUseMainModuleInitializer.value
        val useTest = scalaJSUseTestModuleInitializer.value
        val configName = configuration.value.name

        if (useTest) {
          if (useMain) {
            throw new MessageOnlyException("You may only set one of " +
                s"`$configName / scalaJSUseMainModuleInitializer` " +
                s"`$configName / scalaJSUseTestModuleInitializer` true")
          }

          Seq(
              ModuleInitializer.mainMethod(
                  TestAdapterInitializer.ModuleClassName,
                  TestAdapterInitializer.MainMethodName)
          )
        } else {
          Seq.empty
        }
      },

      loadedTestFrameworks := {
        val configName = configuration.value.name
        val input = jsEnvInput.value

        if (fork.value) {
          throw new MessageOnlyException(
              s"`$configName / test` tasks in a Scala.js project require " +
              s"`$configName / fork := false`.")
        }

        if (!scalaJSUseTestModuleInitializer.value) {
          throw new MessageOnlyException(
              s"You may only use `$configName / test` tasks in a Scala.js project if " +
              s"`$configName / scalaJSUseTestModuleInitializer := true`.")
        }

        if (input.isEmpty) {
          throw new MessageOnlyException(
              s"`$configName / test` got called but `$configName / jsEnvInput` is empty. " +
              "This is not allowed, since running tests requires the generated Scala.js code. " +
              s"If you want to call `$configName / test` but not have it do anything, " +
              s"set `$configName / test` := {}`.")
        }

        val frameworks = testFrameworks.value
        val env = jsEnv.value
        val frameworkNames = frameworks.map(_.implClassNames.toList).toList

        val logger = sbtLogger2ToolsLogger(streams.value.log)
        val config = TestAdapter.Config()
          .withLogger(logger)

        val adapter = newTestAdapter(env, input, config)
        val frameworkAdapters = adapter.loadFrameworks(frameworkNames)

        frameworks.zip(frameworkAdapters).collect {
          case (tf, Some(adapter)) => (tf, adapter)
        }.toMap
      },

      // Override default to avoid triggering a test:fastOptJS in a test:compile
      // without losing autocompletion.
      definedTestNames := {
        definedTests.map(_.map(_.name).distinct)
          .storeAs(definedTestNames).triggeredBy(loadedTestFrameworks).value
      },

      artifactPath in testHtml := {
        val stageSuffix = scalaJSStage.value match {
          case Stage.FastOpt => "fastopt"
          case Stage.FullOpt => "opt"
        }
        val config = configuration.value.name
        ((crossTarget in testHtml).value /
            ((moduleName in testHtml).value + s"-$stageSuffix-$config.html"))
      },

      testHtml := {
        val log = streams.value.log
        val output = (artifactPath in testHtml).value
        val title = name.value + " - tests"
        val input = (jsEnvInput in testHtml).value

        val frameworks = (loadedTestFrameworks in testHtml).value.toList
        val frameworkImplClassNames =
          frameworks.map(_._1.implClassNames.toList)

        val taskDefs = for (td <- (definedTests in testHtml).value) yield {
          new sbt.testing.TaskDef(td.name, td.fingerprint,
              td.explicitlySpecified, td.selectors)
        }

        HTMLRunnerBuilder.writeToFile(output, title, input,
            frameworkImplClassNames, taskDefs.toList)

        log.info(s"Wrote HTML test runner. Point your browser to ${output.toURI}")

        Attributed.blank(output)
      }
  )

  private val scalaJSProjectBaseSettings = Seq(
      platformDepsCrossVersion := ScalaJSCrossVersion.binary,

      scalaJSModuleInitializers := Seq(),
      scalaJSUseMainModuleInitializer := false,
      jsEnvInput := Nil,

      // you will need the Scala.js compiler plugin
      addCompilerPlugin(
          "org.scala-js" % "scalajs-compiler" % scalaJSVersion cross CrossVersion.full),

      libraryDependencies ++= Seq(
          // and of course the Scala.js library
          "org.scala-js" %% "scalajs-library" % scalaJSVersion,
          // as well as the test-bridge in the Test configuration
          "org.scala-js" %% "scalajs-test-bridge" % scalaJSVersion % "test"
      ),

      // and you will want to be cross-compiled on the Scala.js binary version
      crossVersion := ScalaJSCrossVersion.binary
  )

  val scalaJSProjectSettings: Seq[Setting[_]] = (
      scalaJSProjectBaseSettings ++
      inConfig(Compile)(scalaJSCompileSettings) ++
      inConfig(Test)(scalaJSTestSettings)
  )
}
