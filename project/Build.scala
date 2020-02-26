package build

import sbt._
import Keys._

import scala.annotation.tailrec

import com.typesafe.tools.mima.plugin.MimaPlugin.autoImport._
import de.heikoseeberger.sbtheader.HeaderPlugin.autoImport._

import java.io.{
  BufferedOutputStream,
  FileOutputStream
}

import scala.collection.mutable
import scala.util.Properties

import org.scalajs.core.ir
import org.scalajs.core.ir.Utils.escapeJS

import org.scalajs.sbtplugin._
import org.scalajs.jsenv.{JSEnv, RetryingComJSEnv}
import org.scalajs.jsenv.rhino.RhinoJSEnv
import org.scalajs.jsenv.nodejs.{NodeJSEnv, JSDOMNodeJSEnv}
import org.scalajs.jsenv.phantomjs.PhantomJSEnv
import ScalaJSPlugin.autoImport._
import ExternalCompile.scalaJSExternalCompileSettings
import Loggers._

import org.scalajs.core.tools.io.{MemVirtualJSFile, FileVirtualJSFile}
import org.scalajs.core.tools.sem._
import org.scalajs.core.tools.jsdep.ResolvedJSDependency
import org.scalajs.core.tools.json._
import org.scalajs.core.tools.linker.ModuleInitializer

import sbtassembly.AssemblyPlugin.autoImport._

/* In sbt 0.13 the Build trait would expose all vals to the shell, where you
 * can use them in "set a := b" like expressions. This re-exposes them.
 */
object ExposedValues extends AutoPlugin {
  object autoImport {
    val makeCompliant = Build.makeCompliant
  }
}

object Build {

  val isGeneratingForIDE = {
    Properties.envOrElse("GENERATING_ECLIPSE", "false").toBoolean ||
    Properties.envOrElse("METALS_ENABLED", "false").toBoolean
  }

  val bintrayProjectName = settingKey[String](
      "Project name on Bintray")

  val setModuleLoopbackScript = taskKey[Option[ResolvedJSDependency]](
      "In the test suite, under ES modules, the script that sets the " +
      "loopback module namespace")

  val fetchScalaSource = taskKey[File](
    "Fetches the scala source for the current scala version")
  val shouldPartest = settingKey[Boolean](
    "Whether we should partest the current scala version (and fail if we can't)")

  val previousVersion = "0.6.32"
  val previousSJSBinaryVersion =
    ScalaJSCrossVersion.binaryScalaJSVersion(previousVersion)
  val previousBinaryCrossVersion =
    CrossVersion.binaryMapped(v => s"sjs${previousSJSBinaryVersion}_$v")

  def hasNewCollections(version: String): Boolean = {
    !version.startsWith("2.10.") &&
    !version.startsWith("2.11.") &&
    !version.startsWith("2.12.")
  }

  /** Returns the appropriate subdirectory of `sourceDir` depending on the
   *  collection "era" used by the `scalaV`.
   *
   *  It can be the new collections (2.13.x+) or the old collections (until
   *  2.12.x).
   */
  def collectionsEraDependentDirectory(scalaV: String, sourceDir: File): File =
    if (hasNewCollections(scalaV)) sourceDir / "scala-new-collections"
    else sourceDir / "scala-old-collections"

  val scalaVersionsUsedForPublishing: Set[String] =
    Set("2.10.7", "2.11.12", "2.12.10")
  val newScalaBinaryVersionsInThisRelease: Set[String] =
    Set()

  val javaVersion = settingKey[Int](
    "The major Java SDK version that should be assumed for compatibility. " +
    "Defaults to what sbt is running with.")

  val javaDocBaseURL: String = "http://docs.oracle.com/javase/8/docs/api/"

  // set scalaJSSemantics in someProject ~= makeCompliant
  val makeCompliant: Semantics => Semantics = { semantics =>
    semantics
      .withAsInstanceOfs(CheckedBehavior.Compliant)
      .withArrayIndexOutOfBounds(CheckedBehavior.Compliant)
      .withModuleInit(CheckedBehavior.Compliant)
      .withStrictFloats(true)
  }

  private def includeIf(testDir: File, condition: Boolean): List[File] =
    if (condition) List(testDir)
    else Nil

  private def addScalaJSCompilerOption(option: String): Setting[_] =
    addScalaJSCompilerOption(Def.setting(option))

  private def addScalaJSCompilerOption(option: Def.Initialize[String]): Setting[_] =
    addScalaJSCompilerOption(None, option)

  private def addScalaJSCompilerOptionInConfig(config: Configuration,
      option: String): Setting[_] = {
    addScalaJSCompilerOption(Some(config), Def.setting(option))
  }

  private def addScalaJSCompilerOption(config: Option[Configuration],
      option: Def.Initialize[String]): Setting[_] = {
    config.fold(scalacOptions)(scalacOptions in _) ++= {
      if (isGeneratingForIDE) Nil
      else Seq(s"-P:scalajs:${option.value}")
    }
  }

  val previousArtifactSetting: Setting[_] = {
    mimaPreviousArtifacts ++= {
      val scalaV = scalaVersion.value
      val scalaBinaryV = scalaBinaryVersion.value
      if (!scalaVersionsUsedForPublishing.contains(scalaV)) {
        // This artifact will not be published. Binary compatibility is irrelevant.
        Set.empty
      } else if (newScalaBinaryVersionsInThisRelease.contains(scalaBinaryV)) {
        // New in this release, no binary compatibility to comply to
        Set.empty
      } else {
        val thisProjectID = projectID.value
        val previousCrossVersion = thisProjectID.crossVersion match {
          case ScalaJSCrossVersion.binary => previousBinaryCrossVersion
          case crossVersion               => crossVersion
        }
        /* Filter out e:info.apiURL as it expects 0.6.7-SNAPSHOT, whereas the
         * artifact we're looking for has 0.6.6 (for example).
         */
        val prevExtraAttributes =
          thisProjectID.extraAttributes.filterKeys(_ != "e:info.apiURL")
        val prevProjectID =
          (thisProjectID.organization % thisProjectID.name % previousVersion)
            .cross(previousCrossVersion)
            .extra(prevExtraAttributes.toSeq: _*)
        Set(CrossVersion(scalaV, scalaBinaryV)(prevProjectID).cross(CrossVersion.Disabled))
      }
    }
  }

  val commonSettings = Seq(
      scalaVersion := "2.12.10",
      organization := "org.scala-js",
      version := scalaJSVersion,

      normalizedName ~= {
        _.replace("scala.js", "scalajs").replace("scala-js", "scalajs")
      },

      homepage := Some(url("https://www.scala-js.org/")),
      startYear := Some(2013),
      licenses += (("Apache-2.0", url("https://www.apache.org/licenses/LICENSE-2.0"))),
      headerLicense := Some(HeaderLicense.Custom(
        s"""Scala.js (${homepage.value.get})
           |
           |Copyright EPFL.
           |
           |Licensed under Apache License 2.0
           |(https://www.apache.org/licenses/LICENSE-2.0).
           |
           |See the NOTICE file distributed with this work for
           |additional information regarding copyright ownership.
           |""".stripMargin
      )),
      scmInfo := Some(ScmInfo(
          url("https://github.com/scala-js/scala-js"),
          "scm:git:git@github.com:scala-js/scala-js.git",
          Some("scm:git:git@github.com:scala-js/scala-js.git"))),

      shouldPartest := {
        val testListDir = (
          (resourceDirectory in (partestSuite, Test)).value / "scala"
            / "tools" / "partest" / "scalajs" / scalaVersion.value
        )
        testListDir.exists
      },

      scalacOptions ++= Seq(
          "-deprecation",
          "-unchecked",
          "-feature",
          "-encoding", "utf8"
      ),

      // Scaladoc linking
      apiURL := {
        val name = normalizedName.value
        Some(url(s"http://www.scala-js.org/api/$name/$scalaJSVersion/"))
      },
      autoAPIMappings := true,

      // Add Java Scaladoc mapping
      apiMappings ++= {
        val optRTJar = {
          val bootClasspath = System.getProperty("sun.boot.class.path")
          if (bootClasspath != null) {
            // JDK <= 8, there is an rt.jar (or classes.jar) on the boot classpath
            val jars = bootClasspath.split(java.io.File.pathSeparator)
            def matches(path: String, name: String): Boolean =
              path.endsWith(s"${java.io.File.separator}$name.jar")
            val jar = jars.find(matches(_, "rt")) // most JREs
              .orElse(jars.find(matches(_, "classes"))) // Java 6 on Mac OS X
              .get
            Some(file(jar))
          } else {
            // JDK >= 9, maybe sbt gives us a fake rt.jar in `scala.ext.dirs`
            val scalaExtDirs = Option(System.getProperty("scala.ext.dirs"))
            scalaExtDirs.map(extDirs => file(extDirs) / "rt.jar")
          }
        }

        optRTJar.fold[Map[File, URL]] {
          Map.empty
        } { rtJar =>
          assert(rtJar.exists, s"$rtJar does not exist")
          Map(rtJar -> url(javaDocBaseURL))
        }
      },

      /* Add a second Java Scaladoc mapping for cases where Scala actually
       * understands the jrt:/ filesystem of Java 9.
       */
      apiMappings +=
        file("/modules/java.base") -> url(javaDocBaseURL),

      /* Patch the ScalaDoc we generate.
       *
       *  After executing the normal doc command, copy everything to the
       *  `patched-api` directory (same internal directory structure) while
       *  patching the following:
       *
       *  - Append `additional-doc-styles.css` to `lib/template.css`
       *  - Fix external links to the JavaDoc, i.e. change
       *    `${javaDocBaseURL}index.html#java.lang.String` to
       *    `${javaDocBaseURL}index.html?java/lang/String.html`
       */
      doc in Compile := {
        // Where to store the patched docs
        val outDir = crossTarget.value / "patched-api"

        // Find all files in the current docs
        val docPaths = {
          val docDir = (doc in Compile).value
          Path.selectSubpaths(docDir, new SimpleFileFilter(_.isFile)).toMap
        }

        /* File with our CSS styles (needs to be canonical so that the
         * comparison below works)
         */
        val additionalStylesFile =
          (root.base / "assets/additional-doc-styles.css").getCanonicalFile

        // Regex and replacement function for JavaDoc linking
        val javadocAPIRe =
          s"""\"(\\Q${javaDocBaseURL}index.html\\E)#([^"]*)\"""".r

        val logger = streams.value.log
        val errorsSeen = mutable.Set.empty[String]

        val fixJavaDocLink = { (m: scala.util.matching.Regex.Match) =>
          val frag = m.group(2)

          // Fail when encountering links to class members
          if (frag.contains("@") && !errorsSeen.contains(frag)) {
            errorsSeen += frag
            logger.error(s"Cannot fix JavaDoc link to member: $frag")
          }

          m.group(1) + "?" + frag.replace('.', '/') + ".html"
        }

        FileFunction.cached(streams.value.cacheDirectory,
            FilesInfo.lastModified, FilesInfo.exists) { files =>
          for {
            file <- files
            if file != additionalStylesFile
          } yield {
            val relPath = docPaths(file)
            val outFile = outDir / relPath

            if (relPath == "lib/template.css") {
              val styles = IO.read(additionalStylesFile)
              IO.copyFile(file, outFile)
              IO.append(outFile, styles)
            } else if (relPath.endsWith(".html")) {
              val content = IO.read(file)
              val patched = javadocAPIRe.replaceAllIn(content, fixJavaDocLink)
              IO.write(outFile, patched)
            } else {
              IO.copyFile(file, outFile)
            }

            outFile
          }
        } (docPaths.keySet + additionalStylesFile)

        if (errorsSeen.nonEmpty)
          throw new MessageOnlyException("ScalaDoc patching had errors")

        outDir
      }
  )

  val noClassFilesSettings: Setting[_] = {
    scalacOptions in (Compile, compile) += {
      if (isGeneratingForIDE) "-Yskip:jvm"
      else "-Ystop-after:jscode"
    }
  }

  val publishSettings = Seq(
      publishMavenStyle := true,
      publishTo := {
        val nexus = "https://oss.sonatype.org/"
        if (isSnapshot.value)
          Some("snapshots" at nexus + "content/repositories/snapshots")
        else
          Some("releases" at nexus + "service/local/staging/deploy/maven2")
      },
      pomExtra := (
          <developers>
            <developer>
              <id>sjrd</id>
              <name>Sébastien Doeraene</name>
              <url>https://github.com/sjrd/</url>
            </developer>
            <developer>
              <id>gzm0</id>
              <name>Tobias Schlatter</name>
              <url>https://github.com/gzm0/</url>
            </developer>
            <developer>
              <id>nicolasstucki</id>
              <name>Nicolas Stucki</name>
              <url>https://github.com/nicolasstucki/</url>
            </developer>
          </developers>
      ),
      pomIncludeRepository := { _ => false }
  )

  val fatalWarningsSettings = Seq(
      // The pattern matcher used to exceed its analysis budget before 2.11.5
      scalacOptions ++= {
        scalaVersion.value.split('.') match {
          case Array("2", "10", _)                 => Nil
          case Array("2", "11", x)
              if x.takeWhile(_.isDigit).toInt <= 4 => Nil
          case _                                   => Seq("-Xfatal-warnings")
        }
      },

      scalacOptions in (Compile, doc) := {
        val baseOptions = (scalacOptions in (Compile, doc)).value

        // in Scala 2.10, some ScalaDoc links fail
        val fatalInDoc = scalaBinaryVersion.value != "2.10"

        if (fatalInDoc) baseOptions
        else baseOptions.filterNot(_ == "-Xfatal-warnings")
      }
  )

  private def publishToBintraySettings = Seq(
      publishTo := {
        val proj = bintrayProjectName.value
        val ver = version.value
        if (isSnapshot.value) {
          None // Bintray does not support snapshots
        } else {
          val url = new java.net.URL(
              s"https://api.bintray.com/content/scala-js/scala-js-releases/$proj/$ver")
          val patterns = Resolver.ivyStylePatterns
          Some(Resolver.url("bintray", url)(patterns))
        }
      }
  )

  val publishIvySettings = (
      publishToBintraySettings
  ) ++ Seq(
      publishMavenStyle := false
  )

  val myScalaJSSettings = ScalaJSPluginInternal.scalaJSAbstractSettings ++ Seq(
      autoCompilerPlugins := true,
      scalaJSOptimizerOptions ~= (_.withCheckScalaJSIR(true)),

      // Link source maps
      scalacOptions ++= {
        if (isGeneratingForIDE) Seq()
        else if (scalaJSIsSnapshotVersion) Seq()
        else Seq(
          // Link source maps to github sources
          "-P:scalajs:mapSourceURI:" + root.base.toURI +
          "->https://raw.githubusercontent.com/scala-js/scala-js/v" +
          scalaJSVersion + "/"
        )
      },

      addScalaJSCompilerOption("sjsDefinedByDefault")
  )

  private def parallelCollectionsDependencies(
      scalaVersion: String): Seq[ModuleID] = {
    CrossVersion.partialVersion(scalaVersion) match {
      case Some((2, n)) if n >= 13 =>
        Seq("org.scala-lang.modules" %% "scala-parallel-collections" % "0.2.0")

      case _ => Nil
    }
  }

  implicit class ProjectOps(val project: Project) extends AnyVal {
    /** Uses the Scala.js compiler plugin. */
    def withScalaJSCompiler: Project =
      if (isGeneratingForIDE) project
      else project.dependsOn(compiler % "plugin")

    def withScalaJSJUnitPlugin: Project = {
      project.settings(
        scalacOptions in Test ++= {
          if (isGeneratingForIDE) {
            Seq.empty
          } else {
            val jar = (packageBin in (jUnitPlugin, Compile)).value
            Seq(s"-Xplugin:$jar")
          }
        }
      )
    }

    /** Depends on library as if (exportJars in library) was set to false. */
    def dependsOnLibraryNoJar: Project = {
      if (isGeneratingForIDE) {
        project.dependsOn(library)
      } else {
        project.settings(
            internalDependencyClasspath in Compile ++= {
              val prods = (products in (library, Compile)).value
              val analysis = (compile in (library, Compile)).value
              prods.map(p => Classpaths.analyzed(p, analysis))
            }
        )
      }
    }

    /** Depends on the sources of another project. */
    def dependsOnSource(dependency: Project): Project = {
      if (isGeneratingForIDE) {
        project.dependsOn(dependency)
      } else {
        project.settings(
            unmanagedSourceDirectories in Compile +=
              (scalaSource in (dependency, Compile)).value
        )
      }
    }
  }

  val thisBuildSettings = (
      inScope(Global)(ScalaJSPlugin.globalSettings)
  ) ++ Seq(
      // JDK version we are running with
      javaVersion in Global := {
        val fullVersion = System.getProperty("java.version")
        val v = fullVersion.stripPrefix("1.").takeWhile(_.isDigit).toInt
        sLog.value.info(s"Detected JDK version $v")
        if (v < 8)
          throw new MessageOnlyException("This build requires JDK 8 or later. Aborting.")
        v
      }
  )

  lazy val root: Project = Project(
      id = "scalajs",
      base = file("."),
      settings = commonSettings ++ Def.settings(
          name := "Scala.js",
          publishArtifact in Compile := false,

          {
            val allProjects = Seq(
                compiler, irProject, irProjectJS, tools, toolsJS,
                jsEnvs, jsEnvsTestKit, jsEnvsTestSuite, testAdapter, plugin,
                javalanglib, javalib, scalalib, libraryAux, library, javalibEx,
                stubs, cli,
                testInterface, testBridge, jUnitRuntime, jUnitPlugin,
                jUnitTestOutputsJS, jUnitTestOutputsJVM,
                helloworld, reversi, testingExample, testSuite, testSuiteJVM,
                noIrCheckTest, javalibExTestSuite,
                partest, partestSuite,
                scalaTestSuite
            )

            val keys = Seq[TaskKey[_]](
                clean, headerCreate in Compile, headerCreate in Test,
                headerCheck in Compile, headerCheck in Test
            )

            for (key <- keys) yield {
              /* The match is only used to capture the type parameter `a` of
               * each individual TaskKey.
               */
              key match {
                case key: TaskKey[a] =>
                  key := key.dependsOn(allProjects.map(key in _): _*).value
              }
            }
          },

          headerCreate := (headerCreate in Test).dependsOn(headerCreate in Compile).value,
          headerCheck := (headerCheck in Test).dependsOn(headerCheck in Compile).value,

          publish := {},
          publishLocal := {}
      )
  )

  val commonIrProjectSettings = (
      commonSettings ++ publishSettings ++ fatalWarningsSettings
  ) ++ Seq(
      name := "Scala.js IR",
      previousArtifactSetting,
      mimaBinaryIssueFilters ++= BinaryIncompatibilities.IR,
      exportJars := true, // required so ScalaDoc linking works

      testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-s")
  )

  lazy val irProject: Project = Project(
      id = "ir",
      base = file("ir"),
      settings = commonIrProjectSettings ++ Seq(
          libraryDependencies +=
            "com.novocode" % "junit-interface" % "0.9" % "test"
      )
  )

  lazy val irProjectJS: Project = Project(
      id = "irJS",
      base = file("ir/.js"),
      settings = commonIrProjectSettings ++ myScalaJSSettings ++ Seq(
          crossVersion := ScalaJSCrossVersion.binary,
          unmanagedSourceDirectories in Compile +=
            (scalaSource in Compile in irProject).value,
          unmanagedSourceDirectories in Test +=
            (scalaSource in Test in irProject).value
      )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(
      javalibEx, jUnitRuntime % "test", testBridge % "test"
  )

  lazy val compiler: Project = Project(
      id = "compiler",
      base = file("compiler"),
      settings = commonSettings ++ publishSettings ++ Seq(
          name := "Scala.js compiler",
          crossVersion := CrossVersion.full, // because compiler api is not binary compatible
          libraryDependencies ++= Seq(
              "org.scala-lang" % "scala-compiler" % scalaVersion.value,
              "org.scala-lang" % "scala-reflect" % scalaVersion.value,
              "com.novocode" % "junit-interface" % "0.9" % "test"
          ),
          testOptions += Tests.Argument(TestFrameworks.JUnit, "-a"),
          testOptions += Tests.Setup { () =>
            val testOutDir = (streams.value.cacheDirectory / "scalajs-compiler-test")
            IO.createDirectory(testOutDir)
            System.setProperty("scala.scalajs.compiler.test.output",
                testOutDir.getAbsolutePath)
            System.setProperty("scala.scalajs.compiler.test.scalajslib",
                (packageBin in (library, Compile)).value.getAbsolutePath)

            def scalaArtifact(name: String): String = {
              def isTarget(att: Attributed[File]) = {
                att.metadata.get(moduleID.key).exists { mId =>
                  mId.organization == "org.scala-lang" &&
                  mId.name == name &&
                  mId.revision == scalaVersion.value
                }
              }

              (managedClasspath in Test).value.find(isTarget).fold {
                streams.value.log.error(s"Couldn't find $name on the classpath")
                ""
              } { lib =>
                lib.data.getAbsolutePath
              }
            }

            System.setProperty("scala.scalajs.compiler.test.scalalib",
                scalaArtifact("scala-library"))

            System.setProperty("scala.scalajs.compiler.test.scalareflect",
                scalaArtifact("scala-reflect"))
          },
          exportJars := true
      )
  ).dependsOnSource(irProject)

  val commonToolsSettings = (
      commonSettings ++ publishSettings ++ fatalWarningsSettings
  ) ++ Seq(
      name := "Scala.js tools",

      unmanagedSourceDirectories in Compile +=
        baseDirectory.value.getParentFile / "shared/src/main/scala",
      unmanagedSourceDirectories in Compile +=
        collectionsEraDependentDirectory(scalaVersion.value, baseDirectory.value.getParentFile / "shared/src/main"),
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared/src/test/scala",

      if (isGeneratingForIDE) {
        unmanagedSourceDirectories in Compile +=
          baseDirectory.value.getParentFile / "shared/src/main/scala-ide-stubs"
      } else {
        sourceGenerators in Compile += Def.task {
          ScalaJSEnvGenerator.generateEnvHolder(
            baseDirectory.value.getParentFile,
            (sourceManaged in Compile).value)
        }.taskValue
      },

      previousArtifactSetting,
      mimaBinaryIssueFilters ++= BinaryIncompatibilities.Tools,
      exportJars := true // required so ScalaDoc linking works
  )

  lazy val tools: Project = Project(
      id = "tools",
      base = file("tools/jvm"),
      settings = commonToolsSettings ++ Seq(
          libraryDependencies ++= Seq(
              "com.google.javascript" % "closure-compiler" % "v20190513",
              "com.googlecode.json-simple" % "json-simple" % "1.1.1" exclude("junit", "junit"),
              "com.novocode" % "junit-interface" % "0.9" % "test"
          ) ++ (
              parallelCollectionsDependencies(scalaVersion.value)
          )
      )
  ).dependsOn(irProject)

  lazy val toolsJS: Project = Project(
      id = "toolsJS",
      base = file("tools/js"),
      settings = myScalaJSSettings ++ commonToolsSettings ++ Seq(
          crossVersion := ScalaJSCrossVersion.binary,

          /* We need RuntimeClassNameMapper.custom() in QuickLinker
           * TODO Remove this in 1.x.
           */
          scalacOptions in Test -= "-Xfatal-warnings",

          if (isGeneratingForIDE) {
            resourceGenerators in Test ++= Nil
          } else {
            resourceGenerators in Test += Def.task {
              val base = (resourceManaged in Compile).value
              IO.createDirectory(base)
              val outFile = base / "js-test-definitions.js"

              val testDefinitions = {
                org.scalajs.build.HTMLRunnerTemplateAccess.renderTestDefinitions(
                    (loadedTestFrameworks in testSuite in Test).value,
                    (definedTests in testSuite in Test).value)
              }

              IO.write(outFile, testDefinitions)
              Seq(outFile)
            }.taskValue
          },

          // Give more memory to Node.js, and deactivate source maps
          jsEnv := {
            new NodeJSEnv(
                NodeJSEnv.Config()
                  .withArgs(List("--max_old_space_size=3072"))
                  .withSourceMap(false))
          },

          jsDependencies += ProvidedJS / "js-test-definitions.js" % "test"
      ) ++ inConfig(Test) {
        // Redefine test to run Node.js and link HelloWorld
        test := {
          val jsEnv = resolvedJSEnv.value
          if (!jsEnv.isInstanceOf[NodeJSEnv])
            throw new MessageOnlyException("toolsJS/test must be run with Node.js")

          /* Collect IR relevant files from the classpath
           * We assume here that the classpath is valid. This is checked by the
           * the scalaJSIR task.
           */
          val cp = Attributed.data(fullClasspath.value)

          // Files must be Jars, non-files must be dirs
          val (jars, dirs) = cp.filter(_.exists).partition(_.isFile)
          val irFiles = dirs.flatMap(dir => (dir ** "*.sjsir").get)

          def seqOfStringsToJSArrayCode(strings: Seq[String]): String =
            strings.map(s => "\"" + escapeJS(s) + "\"").mkString("[", ", ", "]")

          val irPaths = {
            val absolutePaths = (jars ++ irFiles).map(_.getAbsolutePath)
            seqOfStringsToJSArrayCode(absolutePaths)
          }

          val mainMethods = {
            /* Ideally we would read `scalaJSModuleInitializers in (testSuite, Test)`,
             * but we cannot convert the ModuleInitializers to strings to be
             * passed to the QuickLinker (because ModuleInitializer is a
             * write-only data structure). So we have some duplication.
             */
            val unescapedMainMethods = List(
                "org.scalajs.testsuite.compiler.ModuleInitializerInNoConfiguration.main",
                "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration.main2",
                "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration.main1",
                "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration.mainArgs1()",
                "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration.mainArgs2(foo,bar)"
            )
            seqOfStringsToJSArrayCode(unescapedMainMethods)
          }

          val scalaJSEnv = {
            s"""
            {"javaSystemProperties": {
              "scalajs.scalaVersion": "${scalaVersion.value}",
              "scalajs.bootstrap": "true"
            }}
            """
          }

          val code = {
            s"""
            var linker = ScalaJSQuickLinker;
            var lib = linker.linkTestSuiteNode($irPaths, $mainMethods);

            var __ScalaJSEnv = $scalaJSEnv;

            eval("(function() { 'use strict'; " +
              lib + ";" +
              "ScalaJSTestRunner.runTests();" +
            "}).call(this);");
            """
          }

          val launcher = new MemVirtualJSFile("Generated launcher file")
            .withContent(code)

          val linked = scalaJSLinkedFile.value
          val libs = resolvedJSDependencies.value.data :+
              ResolvedJSDependency.minimal(linked)
          val runner = jsEnv.jsRunner(libs, launcher)

          runner.run(sbtLogger2ToolsLogger(streams.value.log), scalaJSConsole.value)
        }
      }
  ).withScalaJSCompiler.dependsOn(
      javalibEx, testSuite % "test->test", irProjectJS
  )

  lazy val jsEnvs: Project = Project(
      id = "jsEnvs",
      base = file("js-envs"),
      settings = (
          commonSettings ++ publishSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js JS Envs",
          libraryDependencies ++= Seq(
              "org.mozilla" % "rhino" % "1.7.6",
              "org.webjars" % "envjs" % "1.2"
          ) ++ ScalaJSPluginInternal.phantomJSJettyModules.map(_ % "provided"),
          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.JSEnvs
      )
  ).dependsOn(tools)

  lazy val jsEnvsTestKit: Project = Project(
      id = "jsEnvsTestKit",
      base = file("js-envs-test-kit"),
      settings = (
          commonSettings ++ publishSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js JS Envs Test Kit",
          libraryDependencies +=
            "junit" % "junit" % "4.8.2",
          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.JSEnvsTestKit
      )
  ).dependsOn(tools, jsEnvs)

  lazy val jsEnvsTestSuite: Project = Project(
      id = "jsEnvsTestSuite",
      base = file("js-envs-test-suite"),
      settings = (
          commonSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js JS Envs Test Suite",
          libraryDependencies ++= Seq(
              "com.novocode" % "junit-interface" % "0.9" % "test"
          ) ++ ScalaJSPluginInternal.phantomJSJettyModules.map(_ % "provided")
      )
  ).dependsOn(tools, jsEnvs, jsEnvsTestKit % "test")

  lazy val testAdapter = Project(
      id = "testAdapter",
      base = file("test-adapter"),
      settings = (
          commonSettings ++ publishSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js sbt test adapter",
          libraryDependencies += "org.scala-sbt" % "test-interface" % "1.0",
          libraryDependencies +=
            "com.novocode" % "junit-interface" % "0.11" % "test",

          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.TestAdapter,
          unmanagedSourceDirectories in Compile +=
            baseDirectory.value.getParentFile / "test-common/src/main/scala",
          unmanagedSourceDirectories in Test +=
            baseDirectory.value.getParentFile / "test-common/src/test/scala"
      )
  ).dependsOn(jsEnvs)

  lazy val plugin: Project = Project(
      id = "sbtPlugin",
      base = file("sbt-plugin"),
      settings = (
          commonSettings ++ publishIvySettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js sbt plugin",
          normalizedName := "sbt-scalajs",
          bintrayProjectName := "sbt-scalajs-plugin", // "sbt-scalajs" was taken
          sbtPlugin := true,
          sbtVersion in pluginCrossBuild := {
            scalaVersion.value match {
              case v if v.startsWith("2.10.") => "0.13.17"
              case _ => "1.2.1"
            }
          },
          scalaBinaryVersion :=
            CrossVersion.binaryScalaVersion(scalaVersion.value),
          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.SbtPlugin,

          addSbtPlugin("org.portable-scala" % "sbt-platform-deps" % "1.0.0"),

          /* TODO Remove this in 1.x, since there are no macros in sbt-plugin
           * anymore.
           */
          scalacOptions -= "-Xfatal-warnings",

          // Add API mappings for sbt (seems they don't export their API URL)
          apiMappings ++= {
            val deps = (externalDependencyClasspath in Compile).value

            val sbtJars = deps filter { attributed =>
              val p = attributed.data.getPath
              p.contains("/org.scala-sbt/") && p.endsWith(".jar")
            }

            val docUrl =
              url(s"http://www.scala-sbt.org/${sbtVersion.value}/api/")

            sbtJars.map(_.data -> docUrl).toMap
          }
      )
  ).dependsOn(tools, jsEnvs, testAdapter)

  lazy val delambdafySetting = {
    scalacOptions ++= (
        if (isGeneratingForIDE) Seq()
        else if (scalaBinaryVersion.value == "2.10") Seq()
        else Seq("-Ydelambdafy:method"))
  }

  private def serializeHardcodedIR(base: File,
      infoAndTree: (ir.Infos.ClassInfo, ir.Trees.ClassDef)): File = {
    // We assume that there are no weird characters in the full name
    val fullName = ir.Definitions.decodeClassName(infoAndTree._1.encodedName)
    val output = base / (fullName.replace('.', '/') + ".sjsir")

    if (!output.exists()) {
      IO.createDirectory(output.getParentFile)
      val stream = new BufferedOutputStream(new FileOutputStream(output))
      try {
        ir.InfoSerializers.serialize(stream, infoAndTree._1)
        ir.Serializers.serialize(stream, infoAndTree._2)
      } finally {
        stream.close()
      }
    }
    output
  }

  lazy val javalanglib: Project = Project(
      id = "javalanglib",
      base = file("javalanglib"),
      settings = (
          commonSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "java.lang library for Scala.js",
          publishArtifact in Compile := false,
          delambdafySetting,
          noClassFilesSettings,

          /* When writing code in the java.lang package, references to things
           * like `Boolean` or `Double` refer to `j.l.Boolean` or `j.l.Double`.
           * Usually this is not what we want (we want the primitive types
           * instead), but the implicits available in `Predef` hide mistakes by
           * introducing boxing and unboxing where required. The `-Yno-predef`
           * flag prevents these mistakes from happening.
           */
          scalacOptions += "-Yno-predef",

          resourceGenerators in Compile += Def.task {
            val base = (resourceManaged in Compile).value
            Seq(
                serializeHardcodedIR(base, JavaLangObject.InfoAndTree),
                serializeHardcodedIR(base, JavaLangString.InfoAndTree)
            )
          }.taskValue
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).withScalaJSCompiler.dependsOnLibraryNoJar

  lazy val javalib: Project = Project(
      id = "javalib",
      base = file("javalib"),
      settings = (
          commonSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Def.settings(
          name := "Java library for Scala.js",
          publishArtifact in Compile := false,
          delambdafySetting,
          noClassFilesSettings,
          scalaJSExternalCompileSettings,

          /* Do not import `Predef._` so that we have a better control of when
           * we rely on the Scala library.
           */
          scalacOptions += "-Yno-predef",

          headerSources in Compile ~= { srcs =>
            srcs.filter { src =>
              val path = src.getPath.replace('\\', '/')
              !path.contains("/java/math/") &&
              !path.endsWith("/java/util/concurrent/ThreadLocalRandom.scala")
            }
          }
      )
  ).withScalaJSCompiler.dependsOnLibraryNoJar

  lazy val scalalib: Project = Project(
      id = "scalalib",
      base = file("scalalib"),
      settings = commonSettings ++ Seq(
          /* Link source maps to the GitHub sources of the original scalalib
           * #2195 This must come *before* the option added by myScalaJSSettings
           * because mapSourceURI works on a first-match basis.
           */
          addScalaJSCompilerOption(Def.setting {
            "mapSourceURI:" +
            (artifactPath in fetchScalaSource).value.toURI +
            "->https://raw.githubusercontent.com/scala/scala/v" +
            scalaVersion.value + "/src/library/"
          })
      ) ++ myScalaJSSettings ++ Seq(
          name := "Scala library for Scala.js",
          publishArtifact in Compile := false,
          delambdafySetting,
          noClassFilesSettings,

          // The Scala lib is full of warnings we don't want to see
          scalacOptions ~= (_.filterNot(
              Set("-deprecation", "-unchecked", "-feature") contains _)),

          // Tell the plugin to hack-fix bad classOf trees
          addScalaJSCompilerOption("fixClassOf"),

          libraryDependencies +=
            "org.scala-lang" % "scala-library" % scalaVersion.value classifier "sources",

          artifactPath in fetchScalaSource :=
            target.value / "scalaSources" / scalaVersion.value,

          /* Work around for #2649. We would like to always use `update`, but
           * that fails if the scalaVersion we're looking for happens to be the
           * version of Scala used by sbt itself. This is clearly a bug in sbt,
           * which we work around here by using `updateClassifiers` instead in
           * that case.
           */
          update in fetchScalaSource := Def.taskDyn {
            if (scalaVersion.value == scala.util.Properties.versionNumberString)
              updateClassifiers
            else
              update
          }.value,

          fetchScalaSource := {
            val s = streams.value
            val cacheDir = s.cacheDirectory
            val ver = scalaVersion.value
            val trgDir = (artifactPath in fetchScalaSource).value

            val report = (update in fetchScalaSource).value
            val scalaLibSourcesJar = report.select(
                configuration = Set("compile"),
                module = moduleFilter(name = "scala-library"),
                artifact = artifactFilter(classifier = "sources")).headOption.getOrElse {
              throw new Exception(
                  s"Could not fetch scala-library sources for version $ver")
            }

            FileFunction.cached(cacheDir / s"fetchScalaSource-$ver",
                FilesInfo.lastModified, FilesInfo.exists) { dependencies =>
              s.log.info(s"Unpacking Scala library sources to $trgDir...")

              if (trgDir.exists)
                IO.delete(trgDir)
              IO.createDirectory(trgDir)
              IO.unzip(scalaLibSourcesJar, trgDir)
            } (Set(scalaLibSourcesJar))

            trgDir
          },

          unmanagedSourceDirectories in Compile := {
            // Calculates all prefixes of the current Scala version
            // (including the empty prefix) to construct override
            // directories like the following:
            // - override-2.10.2-RC1
            // - override-2.10.2
            // - override-2.10
            // - override-2
            // - override
            val ver = scalaVersion.value
            val base = baseDirectory.value
            val parts = ver.split(Array('.','-'))
            val verList = parts.inits.map { ps =>
              val len = ps.mkString(".").length
              // re-read version, since we lost '.' and '-'
              ver.substring(0, len)
            }
            def dirStr(v: String) =
              if (v.isEmpty) "overrides" else s"overrides-$v"
            val dirs = verList.map(base / dirStr(_)).filter(_.exists)
            dirs.toSeq // most specific shadow less specific
          },

          // Compute sources
          // Files in earlier src dirs shadow files in later dirs
          sources in Compile := {
            // Sources coming from the sources of Scala
            val scalaSrcDir = fetchScalaSource.value

            // All source directories (overrides shadow scalaSrcDir)
            val sourceDirectories =
              (unmanagedSourceDirectories in Compile).value :+ scalaSrcDir

            // Filter sources with overrides
            def normPath(f: File): String =
              f.getPath.replace(java.io.File.separator, "/")

            val sources = mutable.ListBuffer.empty[File]
            val paths = mutable.Set.empty[String]

            for {
              srcDir <- sourceDirectories
              normSrcDir = normPath(srcDir)
              src <- (srcDir ** "*.scala").get
            } {
              val normSrc = normPath(src)
              val path = normSrc.substring(normSrcDir.length)
              val useless =
                path.contains("/scala/collection/parallel/") ||
                path.contains("/scala/util/parsing/")
              if (!useless) {
                if (paths.add(path))
                  sources += src
                else
                  streams.value.log.debug(s"not including $src")
              }
            }

            sources.result()
          },

          headerSources in Compile := Nil,
          headerSources in Test := Nil,

          // Continuation plugin (when using 2.10.x)
          autoCompilerPlugins := true,
          libraryDependencies ++= {
            val ver = scalaVersion.value
            if (ver.startsWith("2.10."))
              Seq(compilerPlugin("org.scala-lang.plugins" % "continuations" % ver))
            else
              Nil
          },
          scalacOptions ++= {
            if (scalaVersion.value.startsWith("2.10."))
              Seq("-P:continuations:enable")
            else
              Nil
          }
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).withScalaJSCompiler.dependsOnLibraryNoJar

  lazy val libraryAux: Project = Project(
      id = "libraryAux",
      base = file("library-aux"),
      settings = (
          commonSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js aux library",
          publishArtifact in Compile := false,
          delambdafySetting,
          noClassFilesSettings
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).withScalaJSCompiler.dependsOnLibraryNoJar

  lazy val library: Project = Project(
      id = "library",
      base = file("library"),
      settings = (
          commonSettings ++ publishSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js library",
          delambdafySetting,
          exportJars := !isGeneratingForIDE,
          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.Library,
          libraryDependencies +=
            "org.scala-lang" % "scala-reflect" % scalaVersion.value % "provided",

          // js.JSApp is annotated with @JSExportDescendentObjects
          addScalaJSCompilerOption("suppressExportDeprecations")
      ) ++ (
          scalaJSExternalCompileSettings
      ) ++ inConfig(Compile)(Seq(
          unmanagedSourceDirectories +=
            collectionsEraDependentDirectory(scalaVersion.value, sourceDirectory.value),

          /* In 2.13 and later, we use the new version of UndefinedBehaviorError
           * which is used in Scala.js 1.x. This is necessary because the old
           * one won't compile anymore due to changes upstream to
           * ControlThrowable. It is also OK to use the new one because 2.13.x
           * requires JDK 8 anyway, and the binary ecosystems are different.
           */
          unmanagedSourceDirectories += {
            val scalaV = scalaVersion.value
            val sourceDir = sourceDirectory.value
            if (scalaV.startsWith("2.10.") || scalaV.startsWith("2.11.") ||
                scalaV.startsWith("2.12.")) {
              sourceDir / "scala-old-ube"
            } else {
              sourceDir / "scala-new-ube"
            }
          },

          scalacOptions in doc ++= Seq(
              "-implicits",
              "-groups",
              "-doc-title", "Scala.js",
              "-doc-version", scalaJSVersion
          ),

          // Filter doc sources to remove implementation details from doc.
          sources in doc := {
            val prev = (sources in doc).value
            val javaV = javaVersion.value
            val scalaV = scalaVersion.value

            /* On Java 9+, Scaladoc will crash with "bad constant pool tag 20"
             * until version 2.12.1 included. The problem seems to have been
             * fixed in 2.12.2, perhaps through
             * https://github.com/scala/scala/pull/5711.
             * See also #3152.
             */
            val mustAvoidJavaDoc = {
              javaV >= 9 && {
                scalaV.startsWith("2.10.") ||
                scalaV.startsWith("2.11.") ||
                scalaV == "2.12.0" ||
                scalaV == "2.12.1"
              }
            }

            if (!mustAvoidJavaDoc) {
              def containsFileFilter(s: String): FileFilter = new FileFilter {
                override def accept(f: File): Boolean = {
                  val path = f.getAbsolutePath.replace('\\', '/')
                  path.contains(s)
                }
              }

              val filter: FileFilter = (
                  AllPassFilter
                    -- containsFileFilter("/scala/scalajs/runtime/")
                    -- containsFileFilter("/scala/scalajs/js/annotation/internal/")
                    -- "*.nodoc.scala"
              )

              (sources in doc).value.filter(filter.accept)
            } else {
              Nil
            }
          },

          /* Add compiled .class files to doc dependencyClasspath, so we can
           * still compile even with only part of the files being present.
           */
          dependencyClasspath in doc ++= exportedProducts.value,

          /* Add the .sjsir files from other lib projects
           * (but not .class files)
           */
          mappings in packageBin := {
            /* From library, we must take everyting, except the
             * java.nio.TypedArrayBufferBridge object, whose actual
             * implementation is in javalib.
             */
            val superMappings = (mappings in packageBin).value
            val libraryMappings = superMappings.filter(
                _._2.replace('\\', '/') !=
                  "scala/scalajs/js/typedarray/TypedArrayBufferBridge$.sjsir")

            val filter = ("*.sjsir": NameFilter)

            val otherProducts = (
                (products in javalanglib).value ++
                (products in javalib).value ++
                (products in scalalib).value ++
                (products in libraryAux).value)
            val otherMappings =
              otherProducts.flatMap(base => Path.selectSubpaths(base, filter))

            libraryMappings ++ otherMappings
          }
      ))
  ).withScalaJSCompiler

  lazy val javalibEx: Project = Project(
      id = "javalibEx",
      base = file("javalib-ex"),
      settings = (
          commonSettings ++ publishSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js JavaLib Ex",
          delambdafySetting,
          noClassFilesSettings,
          exportJars := true,
          jsDependencies +=
            "org.webjars" % "jszip" % "2.4.0" / "jszip.min.js" commonJSName "JSZip"
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).withScalaJSCompiler.dependsOn(library)

  lazy val stubs: Project = Project(
      id = "stubs",
      base = file("stubs"),
      settings = commonSettings ++ publishSettings ++ Seq(
          name := "Scala.js Stubs",
          libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,
          previousArtifactSetting
      )
  )

  // Scala.js command line interface
  lazy val cli: Project = Project(
      id = "cli",
      base = file("cli"),
      settings = (
          commonSettings ++ publishSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js CLI",
          libraryDependencies ++= Seq(
              "com.github.scopt" %% "scopt" % "3.7.1"
          ),

          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.CLI,

          // assembly options
          mainClass in assembly := None, // don't want an executable JAR
          assemblyOption in assembly ~= { _.copy(includeScala = false) },
          assemblyJarName in assembly :=
            s"${normalizedName.value}-assembly_${scalaBinaryVersion.value}-${version.value}.jar"
      )
  ).dependsOn(tools)

  // The Scala.js version of sbt-testing-interface
  lazy val testInterface = Project(
      id = "testInterface",
      base = file("test-interface"),
      settings = (
          commonSettings ++ publishSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js test interface",
          delambdafySetting,
          previousArtifactSetting,
          mimaBinaryIssueFilters ++= BinaryIncompatibilities.TestInterface
      )
  ).withScalaJSCompiler.dependsOn(library)

  lazy val testBridge = Project(
      id = "testBridge",
      base = file("test-bridge"),
      settings = (
          commonSettings ++ publishSettings ++ myScalaJSSettings ++ fatalWarningsSettings
      ) ++ Seq(
          name := "Scala.js test bridge",
          delambdafySetting,
          /* By design, the test-bridge has a completely private API (it is
           * only loaded through a privately-known top-level export), so it
           * does not have `previousArtifactSetting` nor
           * `mimaBinaryIssueFilters`.
           */
          unmanagedSourceDirectories in Compile +=
            baseDirectory.value.getParentFile / "test-common/src/main/scala",
          /* Note: We cannot add the test-common tests, since they test async
           * stuff and JUnit does not support async tests. Therefore we need to
           * block, so we cannot run on JS.
           */

          /* The test bridge uses namespaced top-level exports that we cannot
           * get rid of in 0.6.x.
           */
          addScalaJSCompilerOption("suppressExportDeprecations")
      )
  ).withScalaJSCompiler.dependsOn(library, testInterface)

  lazy val jUnitRuntime = Project(
    id = "jUnitRuntime",
    base = file("junit-runtime"),
    settings = (
        commonSettings ++ publishSettings ++ myScalaJSSettings ++
        fatalWarningsSettings
    ) ++ Def.settings(
        name := "Scala.js JUnit test runtime",

        headerSources in Compile ~= { srcs =>
          srcs.filter { src =>
            val path = src.getPath.replace('\\', '/')
            !path.contains("/org/junit/") && !path.contains("/org/hamcrest/")
          }
        }
    )
  ).withScalaJSCompiler.dependsOn(testInterface)

  val commonJUnitTestOutputsSettings = commonSettings ++ Seq(
      publishArtifact in Compile := false,
      parallelExecution in Test := false,
      unmanagedSourceDirectories in Test +=
        baseDirectory.value.getParentFile / "shared/src/test/scala",
      testOptions in Test ++= Seq(
          Tests.Argument(TestFrameworks.JUnit, "-a", "-s"),
          Tests.Filter(_.endsWith("Assertions"))
      )
  )

  lazy val jUnitTestOutputsJS = Project(
      id = "jUnitTestOutputsJS",
      base = file("junit-test/output-js"),
      settings = commonJUnitTestOutputsSettings ++ myScalaJSSettings ++ Seq(
        name := "Tests for Scala.js JUnit output in JS."
      )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(
      jUnitRuntime % "test", testBridge % "test"
  )


  lazy val jUnitTestOutputsJVM = Project(
      id = "jUnitTestOutputsJVM",
      base = file("junit-test/output-jvm"),
      settings = commonJUnitTestOutputsSettings ++ Seq(
        name := "Tests for Scala.js JUnit output in JVM.",
        libraryDependencies ++= Seq(
            "org.scala-sbt" % "test-interface" % "1.0" % "test",
            "com.novocode" % "junit-interface" % "0.11" % "test"
        )
      )
  )

  lazy val jUnitPlugin = Project(
    id = "jUnitPlugin",
    base = file("junit-plugin"),
    settings = commonSettings ++ publishSettings ++ fatalWarningsSettings ++ Seq(
      name := "Scala.js JUnit test plugin",
      crossVersion := CrossVersion.full,
      libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value,
      exportJars := true
    )
  )

  // Examples

  lazy val examples: Project = Project(
      id = "examples",
      base = file("examples"),
      settings = commonSettings ++ Seq(
          name := "Scala.js examples"
      )
  ).aggregate(helloworld, reversi, testingExample)

  lazy val exampleSettings = commonSettings ++ myScalaJSSettings ++ fatalWarningsSettings ++ Def.settings(
      headerSources in Compile := Nil,
      headerSources in Test := Nil
  )

  lazy val helloworld: Project = Project(
      id = "helloworld",
      base = file("examples") / "helloworld",
      settings = exampleSettings ++ Seq(
          name := "Hello World - Scala.js example",
          moduleName := "helloworld",
          scalaJSUseMainModuleInitializer := true,

          /* We have to test js.JSApp somewhere, so we avoid the fatal
           * deprecation warning here.
           */
          scalacOptions -= "-Xfatal-warnings"
      )
  ).withScalaJSCompiler.dependsOn(library)

  lazy val reversi = Project(
      id = "reversi",
      base = file("examples") / "reversi",
      settings = exampleSettings ++ Seq(
          name := "Reversi - Scala.js example",
          moduleName := "reversi"
      )
  ).withScalaJSCompiler.dependsOn(library)

  lazy val testingExample = Project(
      id = "testingExample",
      base = file("examples") / "testing",
      settings = exampleSettings ++ Seq(
          name := "Testing - Scala.js example",
          moduleName := "testing",

          /* We have a test for test:run which runs a js.JSApp in the Test
           * config. We avoid the fatal deprecation warning here.
           */
          scalacOptions -= "-Xfatal-warnings",

          jsDependencies ++= Seq(
            RuntimeDOMDep(None) % "test",
            "org.webjars" % "jquery" % "1.10.2" / "jquery.js" % "test"
          )
      )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(
      library, jUnitRuntime % "test", testBridge % "test"
  )

  // Testing

  val testTagSettings = {
    val testOptionTags = TaskKey[Seq[String]]("testOptionTags",
        "Task that lists all test options for javaOptions and testOptions.",
        KeyRanks.Invisible)

    Seq(
      testOptionTags := {
        @tailrec
        def envTagsFor(env: JSEnv): Seq[String] = env match {
          case env: RhinoJSEnv =>
            val baseArgs = Seq("rhino")
            if (env.sourceMap) baseArgs :+ "source-maps"
            else baseArgs

          case env: NodeJSEnv =>
            val baseArgs = Seq("nodejs", "typedarray")
            if (env.sourceMap) {
              if (!env.hasSourceMapSupport) {
                throw new MessageOnlyException(
                    "You must install Node.js source map support to " +
                    "run the full Scala.js test suite (npm install " +
                    "source-map-support). To deactivate source map " +
                    "tests, do: set jsEnv in " + thisProject.value.id +
                    " := NodeJSEnv().value.withSourceMap(false)")
              }
              baseArgs :+ "source-maps"
            } else {
              baseArgs
            }

          case env: JSDOMNodeJSEnv =>
            Seq("nodejs.jsdom", "typedarray")

          case _: PhantomJSEnv =>
            Seq("phantomjs")

          case env: RetryingComJSEnv =>
            envTagsFor(env.baseEnv)

          case _ =>
            throw new AssertionError(
                s"Unknown JSEnv of class ${env.getClass.getName}: " +
                "don't know what tags to specify for the test suite")
        }

        val envTags = envTagsFor((resolvedJSEnv in Test).value)

        val stage = (scalaJSStage in Test).value

        val sems = stage match {
          case FastOptStage => (scalaJSSemantics in (Test, fastOptJS)).value
          case FullOptStage => (scalaJSSemantics in (Test, fullOptJS)).value
        }

        val semTags = (
            if (sems.asInstanceOfs == CheckedBehavior.Compliant)
              Seq("compliant-asinstanceofs")
            else
              Seq()
        ) ++ (
            if (sems.arrayIndexOutOfBounds == CheckedBehavior.Compliant)
              Seq("compliant-arrayindexoutofbounds")
            else
              Seq()
        ) ++ (
            if (sems.moduleInit == CheckedBehavior.Compliant)
              Seq("compliant-moduleinit")
            else
              Seq()
        ) ++ (
            if (sems.strictFloats) Seq("strict-floats")
            else Seq()
        ) ++ (
            if (sems.productionMode) Seq("production-mode")
            else Seq("development-mode")
        )

        val stageTag = stage match {
          case FastOptStage => "fastopt-stage"
          case FullOptStage => "fullopt-stage"
        }

        val moduleKindTag = scalaJSModuleKind.value match {
          case ModuleKind.NoModule       => "modulekind-nomodule"
          case ModuleKind.ESModule       => "modulekind-esmodule"
          case ModuleKind.CommonJSModule => "modulekind-commonjs"
        }

        envTags ++ (semTags :+ stageTag :+ moduleKindTag)
      },
      javaOptions in Test ++= {
        def scalaJSProp(name: String): String =
          s"-Dscalajs.$name=true"

        testOptionTags.value.map(scalaJSProp) :+
            "-Dscalajs.testsuite.testtag=testtag.value"
      },
      testOptions in Test ++= {
        def testArgument(arg: String): Tests.Argument =
          Tests.Argument("-t" + arg)

        testOptionTags.value.map(testArgument)
      }
    )
  }

  def testSuiteCommonSettings(isJSTest: Boolean): Seq[Setting[_]] = Seq(
    publishArtifact in Compile := false,
    scalacOptions ~= (_.filter(_ != "-deprecation")),

    // To support calls to static methods in interfaces
    scalacOptions in Test ++= {
      /* Starting from 2.10.7 and 2.11.12, scalac refuses to emit calls to
       * static methods in interfaces unless the -target:jvm-1.8 flag is given.
       * scalac 2.12+ emits JVM 8 bytecode by default, of course, so it is not
       * needed for later versions.
       */
      val PartialVersion = """(\d+)\.(\d+)\.(\d+)(?:-.+)?""".r
      val needsTargetFlag = scalaVersion.value match {
        case PartialVersion("2", "10", n) => n.toInt >= 7
        case PartialVersion("2", "11", n) => n.toInt >= 12
        case _                            => false
      }
      if (needsTargetFlag)
        Seq("-target:jvm-1.8")
      else
        Nil
    },

    // Need reflect for typechecking macros
    libraryDependencies +=
      "org.scala-lang" % "scala-reflect" % scalaVersion.value % "provided",

    testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-s"),

    unmanagedSourceDirectories in Test ++= {
      val testDir = (sourceDirectory in Test).value
      val sharedTestDir =
        testDir.getParentFile.getParentFile.getParentFile / "shared/src/test"

      val scalaV = scalaVersion.value
      val isScalaAtLeast212 =
        !scalaV.startsWith("2.10.") && !scalaV.startsWith("2.11.")

      List(sharedTestDir / "scala", sharedTestDir / "require-jdk7",
          sharedTestDir / "require-jdk8") ++
      includeIf(testDir / "require-2.12", isJSTest && isScalaAtLeast212)
    },

    sources in Test ++= {
      val supportsSAM = scalaBinaryVersion.value match {
        case "2.10" => false
        case "2.11" => scalacOptions.value.contains("-Xexperimental")
        case _      => true
      }

      val scalaV = scalaVersion.value

      /* Can't add require-sam as unmanagedSourceDirectories because of the use
       * of scalacOptions. Hence sources are added individually.
       * Note that a testSuite/test will not trigger a compile when sources are
       * modified in require-sam
       */
      if (supportsSAM) {
        val testDir = (sourceDirectory in Test).value
        val sharedTestDir =
          testDir.getParentFile.getParentFile.getParentFile / "shared/src/test"

        val allSAMSources = {
          ((sharedTestDir / "require-sam") ** "*.scala").get ++
          (if (isJSTest) ((testDir / "require-sam") ** "*.scala").get else Nil)
        }

        val hasBugWithOverriddenMethods =
          Set("2.12.0", "2.12.1", "2.12.2", "2.12.3", "2.12.4").contains(scalaV)

        if (hasBugWithOverriddenMethods)
          allSAMSources.filter(_.getName != "SAMWithOverridingBridgesTest.scala")
        else
          allSAMSources
      } else {
        Nil
      }
    }
  )

  def testHtmlSettings[T](testHtmlKey: TaskKey[T], targetStage: Stage) = Seq(
      // We need to patch the system properties.
      scalaJSJavaSystemProperties in Test in testHtmlKey ~= { base =>
        val unsupported =
          Seq("rhino", "nodejs", "nodejs.jsdom", "phantomjs", "source-maps")
        val supported =
          Seq("typedarray", "browser")

        base -- unsupported.map("scalajs." + _) ++
            supported.map("scalajs." + _ -> "true")
      },

      // Fail if we are not in the right stage.
      testHtmlKey in Test := (testHtmlKey in Test).dependsOn(Def.task {
        if (scalaJSStage.value != targetStage) {
          throw new MessageOnlyException(
              "In the Scala.js test-suite, the testHtml* tasks need " +
              "scalaJSStage to be set to their respecitve stage. Stage is: " +
              scalaJSStage.value)
        }
      }).value
  )

  lazy val testSuite: Project = Project(
    id = "testSuite",
    base = file("test-suite/js"),
    settings = commonSettings ++ myScalaJSSettings ++ testTagSettings ++
      testSuiteCommonSettings(isJSTest = true) ++
      testHtmlSettings(testHtmlFastOpt, FastOptStage) ++
      testHtmlSettings(testHtmlFullOpt, FullOptStage) ++ Seq(
        name := "Scala.js test suite",

        /* We still have zillions of run test for top-level @JSExport and for
         * @JSName/missing @JSGlobal. Don't drown the test:compile output under
         * useless warnings.
         */
        addScalaJSCompilerOptionInConfig(Test, "suppressExportDeprecations"),
        addScalaJSCompilerOptionInConfig(Test, "suppressMissingJSGlobalDeprecations"),

        unmanagedSourceDirectories in Test ++= {
          val testDir = (sourceDirectory in Test).value
          val scalaV = scalaVersion.value

          collectionsEraDependentDirectory(scalaV, testDir) ::
          includeIf(testDir / "require-modules",
              scalaJSModuleKind.value != ModuleKind.NoModule) :::
          includeIf(testDir / "require-dynamic-import",
              scalaJSModuleKind.value == ModuleKind.ESModule) // this is an approximation that works for now
        },

        jsDependencies += ProvidedJS / "ScalaJSDefinedTestNatives.js" % "test",
        skip in packageJSDependencies in Test := false,

        scalaJSSemantics ~= { sems =>
          import Semantics.RuntimeClassNameMapper

          sems.withRuntimeClassNameMapper(
              RuntimeClassNameMapper.custom(_.fullName match {
                case "org.scalajs.testsuite.compiler.ReflectionTest$RenamedTestClass" =>
                  "renamed.test.Class"
                case fullName =>
                  fullName
              }).andThen(
                  RuntimeClassNameMapper.regexReplace(
                      raw"""^org\.scalajs\.testsuite\.compiler\.ReflectionTest\$$Prefix""".r,
                      "renamed.test.byprefix.")
              ).andThen(
                  RuntimeClassNameMapper.regexReplace(
                      raw"""^org\.scalajs\.testsuite\.compiler\.ReflectionTest\$$OtherPrefix""".r,
                      "renamed.test.byotherprefix.")
              )
          )
        },

        javaOptions in Test += "-Dscalajs.scalaVersion=" + scalaVersion.value,

        /* The script that calls setExportsNamespaceForExportsTest to provide
         * ExportsTest with a loopback reference to its own exports namespace.
         * Only when using an ES module.
         * See the comment in ExportsTest for more details.
         */
        setModuleLoopbackScript in Test := Def.settingDyn[Task[Option[ResolvedJSDependency]]] {
          (scalaJSModuleKind in Test).value match {
            case ModuleKind.ESModule =>
              Def.task {
                val linkedFile =
                  (scalaJSLinkedFile in Test).value.asInstanceOf[FileVirtualJSFile].file
                val uri = linkedFile.toURI.toASCIIString

                val setNamespaceScriptFile =
                  crossTarget.value / (linkedFile.getName + "-loopback.js")

                /* Due to the asynchronous nature of ES module loading, there
                 * exists a theoretical risk for a race condition here. It is
                 * possible that tests will start running and reaching the
                 * ExportsTest before the callback in this script is executed.
                 * It's quite unlikely, though, given all the message passing
                 * for the com and all that.
                 */
                IO.write(setNamespaceScriptFile,
                    s"""
                      |(function() {
                      |  "use strict";
                      |  import("${escapeJS(uri)}").then(mod => {
                      |    mod.setExportsNamespaceForExportsTest(mod);
                      |  });
                      |})();
                    """.stripMargin)

                val vf = FileVirtualJSFile(setNamespaceScriptFile)
                Some(ResolvedJSDependency.minimal(vf))
              }

            case _ =>
              Def.task {
                None
              }
          }
        }.value,

        scalaJSConfigurationLibs in Test ++=
          (setModuleLoopbackScript in Test).value.toList,

        /* Generate a scala source file that throws exceptions in
         * various places (while attaching the source line to the
         * exception). When we catch the exception, we can then
         * compare the attached source line and the source line
         * calculated via the source maps.
         *
         * see test-suite/src/test/resources/SourceMapTestTemplate.scala
         */
        sourceGenerators in Test += Def.task {
          val dir = (sourceManaged in Test).value
          IO.createDirectory(dir)

          val template = IO.read((resourceDirectory in Test).value /
            "SourceMapTestTemplate.scala")

          def lineNo(cs: CharSequence) =
            (0 until cs.length).count(i => cs.charAt(i) == '\n') + 1

          var i = 0
          val pat = "/\\*{2,3}/".r
          val replaced = pat.replaceAllIn(template, { mat =>
            val lNo = lineNo(mat.before)
            val res =
              if (mat.end - mat.start == 5)
                // matching a /***/
                s"if (TC.is($i)) { throw new TestException($lNo) } else "
              else
                // matching a /**/
                s"; if (TC.is($i)) { throw new TestException($lNo) } ;"

            i += 1

            res
          })

          val outFile = dir / "SourceMapTest.scala"
          val unitTests =
            (0 until i).map(i => s"@Test def workTest$i(): Unit = test($i)").mkString("; ")
          IO.write(outFile,
              replaced.replace("@Test def workTest(): Unit = ???", unitTests))
          Seq(outFile)
        }.taskValue,

        // Exclude tests based on version-dependent bugs
        sources in Test := {
          val sourceFiles = (sources in Test).value
          val v = scalaVersion.value

          val hasBug2382 = v.startsWith("2.10.") || v.startsWith("2.11.")
          val sourceFiles1 = {
            if (hasBug2382)
              sourceFiles.filterNot(_.getName == "OuterClassTest.scala")
            else
              sourceFiles
          }

          sourceFiles1
        },

        /* Reduce the amount of tests on PhantomJS to avoid a crash.
         * It seems we reached the limits of what PhantomJS can handle in terms
         * of code mass. Since PhantomJS support is due to be moved to a
         * separate repository in 1.0.0, the easiest way to fix this is to
         * reduce the pressure on PhantomJS. We therefore remove the tests of
         * java.math (BigInteger and BigDecimal) when running with PhantomJS.
         * These tests are well isolated, and the less likely to have
         * environmental differences.
         *
         * Note that `jsEnv` is never set from this Build, but it is set via
         * the command-line in the CI matrix.
         */
        sources in Test := {
          def isPhantomJS(env: JSEnv): Boolean = env match {
            case _: PhantomJSEnv       => true
            case env: RetryingComJSEnv => isPhantomJS(env.baseEnv)
            case _                     => false
          }

          val sourceFiles = (sources in Test).value
          if ((jsEnv in Test).?.value.exists(isPhantomJS)) {
            sourceFiles.filter { f =>
              val path = f.getAbsolutePath.replace('\\', '/')

              {
                !path.contains("/org/scalajs/testsuite/javalib/math/") &&
                !path.contains("/org/scalajs/testsuite/niocharset/") &&
                !path.contains("/src/test/require-")
              }
            }
          } else {
            sourceFiles
          }
        },

        // Module initializers. Duplicated in toolsJS/test
        scalaJSModuleInitializers += {
          ModuleInitializer.mainMethod(
              "org.scalajs.testsuite.compiler.ModuleInitializerInNoConfiguration",
              "main")
        },
        scalaJSModuleInitializers in Compile += {
          ModuleInitializer.mainMethod(
              "org.scalajs.testsuite.compiler.ModuleInitializerInCompileConfiguration",
              "main")
        },
        scalaJSModuleInitializers in Test += {
          ModuleInitializer.mainMethod(
              "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration",
              "main2")
        },
        scalaJSModuleInitializers in Test += {
          ModuleInitializer.mainMethod(
              "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration",
              "main1")
        },
        scalaJSModuleInitializers in Test += {
          ModuleInitializer.mainMethodWithArgs(
              "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration",
              "mainArgs1")
        },
        scalaJSModuleInitializers in Test += {
          ModuleInitializer.mainMethodWithArgs(
              "org.scalajs.testsuite.compiler.ModuleInitializerInTestConfiguration",
              "mainArgs2", List("foo", "bar"))
        }
      )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(
    library, jUnitRuntime, testBridge % "test"
  )

  lazy val testSuiteJVM: Project = Project(
    id = "testSuiteJVM",
    base = file("test-suite/jvm"),
    settings = commonSettings ++ testSuiteCommonSettings(isJSTest = false) ++ Seq(
      name := "Scala.js test suite on JVM",

      /* Scala.js always assumes en-US, UTF-8 and NL as line separator by
       * default. Since some of our tests rely on these defaults (notably to
       * test them), we have to force the same values on the JVM.
       */
      fork in Test := true,
      javaOptions in Test ++= Seq(
          "-Dfile.encoding=UTF-8",
          "-Duser.country=US", "-Duser.language=en",
          "-Dline.separator=\n"
      ),

      libraryDependencies +=
        "com.novocode" % "junit-interface" % "0.11" % "test"
    )
  )

  lazy val noIrCheckTest: Project = Project(
      id = "noIrCheckTest",
      base = file("no-ir-check-test"),
      settings = commonSettings ++ myScalaJSSettings ++ testTagSettings ++ Seq(
          name := "Scala.js not IR checked tests",
          scalaJSOptimizerOptions ~= (_.
              withCheckScalaJSIR(false).
              withBypassLinkingErrors(true)
          ),
          testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-s"),
          publishArtifact in Compile := false
     )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(library, jUnitRuntime, testBridge % "test")

  lazy val javalibExTestSuite: Project = Project(
      id = "javalibExTestSuite",
      base = file("javalib-ex-test-suite"),
      settings = (
          commonSettings ++ myScalaJSSettings ++ testTagSettings
      ) ++ Seq(
          name := "JavaLib Ex Test Suite",
          publishArtifact in Compile := false,
          testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-s"),
          scalacOptions in Test ~= (_.filter(_ != "-deprecation"))
      )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(javalibEx, jUnitRuntime, testBridge % "test")

  lazy val partest: Project = Project(
      id = "partest",
      base = file("partest"),
      settings = commonSettings ++ fatalWarningsSettings ++ Seq(
          name := "Partest for Scala.js",
          moduleName := "scalajs-partest",

          resolvers += Resolver.typesafeIvyRepo("releases"),

          artifactPath in fetchScalaSource :=
            baseDirectory.value / "fetchedSources" / scalaVersion.value,

          fetchScalaSource := {
            import org.eclipse.jgit.api._

            val s = streams.value
            val ver = scalaVersion.value
            val trgDir = (artifactPath in fetchScalaSource).value

            if (!trgDir.exists) {
              s.log.info(s"Fetching Scala source version $ver")

              // Make parent dirs and stuff
              IO.createDirectory(trgDir)

              // Clone scala source code
              new CloneCommand()
                .setDirectory(trgDir)
                .setURI("https://github.com/scala/scala.git")
                .call()
            }

            // Checkout proper ref. We do this anyway so we fail if
            // something is wrong
            val git = Git.open(trgDir)
            s.log.info(s"Checking out Scala source version $ver")
            git.checkout().setName(s"v$ver").call()

            trgDir
          },

          libraryDependencies ++= {
            if (shouldPartest.value) {
              Seq(
                  "org.scala-sbt" % "sbt" % sbtVersion.value,
                  {
                    val v = scalaVersion.value
                    if (v == "2.11.0" || v == "2.11.1" || v == "2.11.2")
                      "org.scala-lang.modules" %% "scala-partest" % "1.0.13"
                    else if (v.startsWith("2.11."))
                      "org.scala-lang.modules" %% "scala-partest" % "1.0.16"
                    else
                      "org.scala-lang.modules" %% "scala-partest" % "1.1.4"
                  },
                  "com.google.javascript" % "closure-compiler" % "v20190513",
                  "org.mozilla" % "rhino" % "1.7.6",
                  "com.googlecode.json-simple" % "json-simple" % "1.1.1" exclude("junit", "junit")
              ) ++ (
                  parallelCollectionsDependencies(scalaVersion.value)
              )
            } else {
              Seq()
            }
          },

          unmanagedSourceDirectories in Compile += {
            val sourceRoot = (sourceDirectory in Compile).value.getParentFile
            val v = scalaVersion.value
            if (v == "2.11.0" || v == "2.11.1" || v == "2.11.2")
              sourceRoot / "main-partest-1.0.13"
            else
              sourceRoot / "main-partest-1.0.16"
          },

          sources in Compile := {
            if (shouldPartest.value) {
              // Partest sources and some sources of sbtplugin (see above)
              val baseSrcs = (sources in Compile).value
              // Sources for tools (and hence IR)
              val toolSrcs = (sources in (tools, Compile)).value
              // Sources for js-envs
              val jsenvSrcs = {
                val jsenvBase = ((scalaSource in (jsEnvs, Compile)).value /
                  "org/scalajs/jsenv")

                val scalaFilter: FileFilter = "*.scala"
                val files = (
                    (jsenvBase * scalaFilter) +++
                    (jsenvBase / "nodejs" ** scalaFilter) +++
                    (jsenvBase / "rhino" ** scalaFilter))

                files.get
              }
              toolSrcs ++ baseSrcs ++ jsenvSrcs
            } else Seq()
          }

      )
  ).dependsOn(compiler)

  lazy val partestSuite: Project = Project(
      id = "partestSuite",
      base = file("partest-suite"),
      settings = commonSettings ++ fatalWarningsSettings ++ Seq(
          name := "Scala.js partest suite",

          fork in Test := true,
          javaOptions in Test += "-Xmx1G",

          // Override the dependency of partest - see #1889
          dependencyOverrides += "org.scala-lang" % "scala-library" % scalaVersion.value % "test",

          testFrameworks ++= {
            if (shouldPartest.value)
              Seq(new TestFramework("scala.tools.partest.scalajs.Framework"))
            else Seq()
          },

          definedTests in Test ++= Def.taskDyn[Seq[sbt.TestDefinition]] {
            if (shouldPartest.value) Def.task {
              val _ = (fetchScalaSource in partest).value
              Seq(new sbt.TestDefinition(
                s"partest-${scalaVersion.value}",
                // marker fingerprint since there are no test classes
                // to be discovered by sbt:
                new sbt.testing.AnnotatedFingerprint {
                  def isModule = true
                  def annotationName = "partest"
                },
                true,
                Array()
              ))
            } else {
              Def.task(Seq())
            }
          }.value
      )
  ).dependsOn(partest % "test", library)

  lazy val scalaTestSuite: Project = Project(
    id = "scalaTestSuite",
    base = file("scala-test-suite"),
    settings = commonSettings ++ myScalaJSSettings ++ Seq(
      publishArtifact in Compile := false,

      testOptions += Tests.Argument(TestFrameworks.JUnit, "-a", "-s"),

      unmanagedSources in Compile ++= {
        val scalaV = scalaVersion.value
        val upstreamSrcDir = (fetchScalaSource in partest).value

        if (scalaV.startsWith("2.10.") || scalaV.startsWith("2.11.") ||
            scalaV.startsWith("2.12.")) {
          Nil
        } else {
          List(upstreamSrcDir / "src/testkit/scala/tools/testkit/AssertUtil.scala")
        }
      },

      unmanagedSources in Test ++= {
        assert(scalaBinaryVersion.value != "2.10",
            "scalaTestSuite is not supported on Scala 2.10")

        def loadList(listName: String): Set[String] = {
          val listsDir = (resourceDirectory in Test).value / scalaVersion.value
          val buff = scala.io.Source.fromFile(listsDir / listName)
          val lines = buff.getLines().collect {
            case line if !line.startsWith("#") && line.nonEmpty => line
          }.toSeq
          val linesSet = lines.toSet
          if (linesSet.size != lines.size) {
            val msg = listName + " contains contains duplicates: " +
                lines.diff(linesSet.toSeq).toSet
            throw new AssertionError(msg.toString)
          }
          linesSet
        }

        val whitelist: Set[String] = loadList("WhitelistedTests.txt")
        val blacklist: Set[String] = loadList("BlacklistedTests.txt")

        val jUnitTestsPath =
          (fetchScalaSource in partest).value / "test" / "junit"

        val scalaScalaJUnitSources = {
          (jUnitTestsPath ** "*.scala").get.flatMap { file =>
            file.relativeTo(jUnitTestsPath) match {
              case Some(rel) => List((rel.toString.replace('\\', '/'), file))
              case None      => Nil
            }
          }
        }

        // Check the coherence of the lists against the files found.
        val allClasses = scalaScalaJUnitSources.map(_._1).toSet
        val inBothLists = blacklist.intersect(whitelist)
        val allListed = blacklist.union(whitelist)
        val inNoList = allClasses.diff(allListed)
        val nonexistentBlacklisted = blacklist.diff(allClasses)
        val nonexistentWhitelisted = whitelist.diff(allClasses)
        if (inBothLists.nonEmpty || inNoList.nonEmpty ||
            nonexistentBlacklisted.nonEmpty || nonexistentWhitelisted.nonEmpty) {
          val msg = new StringBuffer("Errors in black or white lists.\n")
          if (inBothLists.nonEmpty) {
            msg.append("Sources listed both in black and white list: ")
            msg.append(inBothLists).append('\n')
          }
          if (inNoList.nonEmpty) {
            msg.append("Sources not listed in back or white list: ")
            msg.append(inNoList).append('\n')
          }
          if (nonexistentBlacklisted.nonEmpty) {
            msg.append("Sources not found for blacklisted tests: ")
            msg.append(nonexistentBlacklisted).append('\n')
          }
          if (nonexistentWhitelisted.nonEmpty) {
            msg.append("Sources not found for whitelisted tests: ")
            msg.append(nonexistentWhitelisted).append('\n')
          }
          throw new AssertionError(msg.toString)
        }

        scalaScalaJUnitSources.collect {
          case fTup if whitelist(fTup._1) => fTup._2
        }
      },

      /* Disable slow tests when running with Rhino, because they become *too*
       * slow with Rhino.
       *
       * The following tests are targeted:
       *
       * - immutable.RangeConsistencyTest.rangeChurnTest
       * - immutable.SetTest.t7326
       * - immutable.TreeSeqMapTest.testAppend
       * - mutable.ArrayDequeTest.apply
       * - mutable.ArrayDequeTest.sliding
       * - mutable.QueueTest.sliding
       * - mutable.StackTest.sliding
       *
       * Unfortunately we cannot disable test by test, so we have to disable
       * the whole class instead.
       */
      testOptions in Test := {
        val prev = (testOptions in Test).value
        val isRhino = (resolvedJSEnv in Test).value.isInstanceOf[RhinoJSEnv]
        if (isRhino) {
          prev :+ Tests.Filter { name =>
            !name.endsWith(".immutable.RangeConsistencyTest") &&
            !name.endsWith(".immutable.SetTest") &&
            !name.endsWith(".immutable.TreeSeqMapTest") &&
            !name.endsWith(".mutable.ArrayDequeTest") &&
            !name.endsWith(".mutable.QueueTest") &&
            !name.endsWith(".mutable.StackTest")
          }
        } else {
          prev
        }
      }
    )
  ).withScalaJSCompiler.withScalaJSJUnitPlugin.dependsOn(jUnitRuntime, testBridge % "test")

}
