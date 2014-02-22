import sbt._
import Keys._

import PublishToBintray.publishToBintraySettings

import scala.util.Properties

import scala.scalajs.sbtplugin._
import ScalaJSPlugin._
import ScalaJSKeys._
import SourceMapCat.catJSFilesAndTheirSourceMaps
import ExternalCompile.scalaJSExternalCompileSettings

object ScalaJSBuild extends Build {

  val commonSettings = Defaults.defaultSettings ++ Seq(
      organization := "org.scala-lang.modules.scalajs",
      version := scalaJSVersion,

      normalizedName ~= {
        _.replace("scala.js", "scalajs").replace("scala-js", "scalajs")
      },

      homepage := Some(url("http://scala-js.org/")),
      licenses += ("BSD New",
          url("https://github.com/scala-js/scala-js/blob/master/LICENSE"))
  )

  private val snapshotsOrReleases =
    if (scalaJSIsSnapshotVersion) "snapshots" else "releases"

  private def publishToScalaJSRepoSettings = Seq(
      publishTo := {
        Seq("PUBLISH_USER", "PUBLISH_PASS").map(Properties.envOrNone) match {
          case Seq(Some(user), Some(pass)) =>
            Some(Resolver.sftp(
                s"scala-js-$snapshotsOrReleases",
                "repo.scala-js.org",
                s"/home/scalajsrepo/www/repo/$snapshotsOrReleases")(
                Resolver.ivyStylePatterns) as (user, pass))
          case _ =>
            None
        }
      }
  )

  val publishSettings = (
      if (Properties.envOrNone("PUBLISH_TO_BINTRAY") == Some("true"))
        publishToBintraySettings
      else
        publishToScalaJSRepoSettings
  ) ++ Seq(
      publishMavenStyle := false
  )

  val defaultSettings = commonSettings ++ Seq(
      scalaVersion := scalaJSScalaVersion,
      scalacOptions ++= Seq(
          "-deprecation",
          "-unchecked",
          "-feature",
          "-encoding", "utf8"
      )
  )

  val myScalaJSSettings = scalaJSAbstractSettings ++ Seq(
      autoCompilerPlugins := true
  )

  // Used when compiling the compiler, adding it to scalacOptions does not help
  scala.util.Properties.setProp("scalac.patmat.analysisBudget", "1024")

  override lazy val settings = super.settings ++ Seq(
    // Most of the projects cross-compile
    crossScalaVersions := Seq("2.10.3", "2.11.0-M8"),

    /* Friendly error message when we forget to fetch the submodule
     * or when we forget to update it after changing branch. */
    {
      val f = (s: State) => {
        val logger = s.globalLogging.full
        import logger.warn
        val base = s.configuration.baseDirectory()
        for {
          (ver, expectedSha) <- Seq(
              "2.10" -> "e2fec6b28dfd73482945ffab85d9b582d0cb9f17",
              "2.11" -> "8f6f4032b5c026fd9301cebe28dde5bb7c8e264c"
          )
        } {
          val scalalibHeadFile = base / s".git/modules/scalalib/source-$ver/HEAD"
          if (!scalalibHeadFile.exists()) {
            warn(s"It seems you have not fetched the scalalib/source-$ver submodule.")
            warn("This will prevent you from building Scala.js!")
            warn("You can fix this by doing the following:")
            warn("  $ git submodule init")
            warn("  $ git submodule update")
          } else {
            val sha = IO.readLines(scalalibHeadFile).headOption
            if (sha != Some(expectedSha)) {
              warn(s"The head of the scala/source-$ver submodule is not the one I expected.")
              warn("This will likely prevent you from building Scala.js and will cause weird errors!")
              warn("You can fix this by doing the following:")
              warn("  $ git submodule update")
            }
          }
        }
        s
      }
      onLoad in Global := {
        val previous = (onLoad in Global).value
        f compose previous
      }
    }
  )

  lazy val root: Project = Project(
      id = "scalajs",
      base = file("."),
      settings = defaultSettings ++ Seq(
          name := "Scala.js",
          publishArtifact in Compile := false,

          clean := clean.dependsOn(
              // compiler, library and jasmineTestFramework are aggregated
              clean in plugin, clean in corejslib, clean in javalib,
              clean in scalalib, clean in libraryAux, clean in test,
              clean in examples, clean in exampleHelloWorld,
              clean in exampleReversi, clean in exampleTesting).value,

          publish := {},
          publishLocal := {}
      )
  ).aggregate(
      compiler, library, jasmineTestFramework
  )

  lazy val compiler: Project = Project(
      id = "scalajs-compiler",
      base = file("compiler"),
      settings = defaultSettings ++ publishSettings ++ Seq(
          name := "Scala.js compiler",
          libraryDependencies ++= Seq(
              "org.scala-lang" % "scala-compiler" % scalaVersion.value,
              "org.scala-lang" % "scala-reflect" % scalaVersion.value
          ),
          exportJars := true
      )
  )

  lazy val plugin: Project = Project(
      id = "scalajs-sbt-plugin",
      base = file("sbt-plugin"),
      settings = commonSettings ++ publishSettings ++ Seq(
          name := "Scala.js sbt plugin",
          sbtPlugin := true,
          scalaBinaryVersion :=
            CrossVersion.binaryScalaVersion(scalaVersion.value),
          libraryDependencies ++= Seq(
              "com.google.javascript" % "closure-compiler" % "v20130603",
              "org.mozilla" % "rhino" % "1.7R4"
          )
      )
  )

  lazy val corejslib: Project = Project(
      id = "scalajs-corejslib",
      base = file("corejslib"),
      settings = defaultSettings ++ Seq(
          name := "Scala.js core JS runtime",
          publishArtifact in Compile := false,

          packageJS in Compile := {
            val s = streams.value
            val targetDir = (target in Compile).value

            // hard-coded because order matters!
            val fileNames =
              Seq("scalajsenv.js", "javalangObject.js",
                  "javalangString.js", "DummyParents.js")

            val allJSFiles = fileNames map (baseDirectory.value / _)
            val output = targetDir / ("scalajs-corejslib.js")

            FileFunction.cached(s.cacheDirectory / "package-js",
                FilesInfo.lastModified, FilesInfo.exists) { dependencies =>
              targetDir.mkdir()
              catJSFilesAndTheirSourceMaps(allJSFiles, output, false)
              Set(output)
            } (allJSFiles.toSet)

            Seq(output)
          }
      )
  )

  lazy val delambdafySetting = {
    scalacOptions ++= (
        if (scalaBinaryVersion.value == "2.10") Seq()
        else Seq("-Ydelambdafy:method"))
  }

  lazy val javalib: Project = Project(
      id = "scalajs-javalib",
      base = file("javalib"),
      settings = defaultSettings ++ myScalaJSSettings ++ Seq(
          name := "Java library for Scala.js",
          publishArtifact in Compile := false,
          delambdafySetting,
          scalacOptions += "-Yskip:cleanup,icode,jvm"
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).dependsOn(compiler % "plugin", library)

  lazy val scalalib: Project = Project(
      id = "scalajs-scalalib",
      base = file("scalalib"),
      settings = defaultSettings ++ myScalaJSSettings ++ Seq(
          name := "Scala library for Scala.js",
          publishArtifact in Compile := false,
          delambdafySetting,

          // The Scala lib is full of warnings we don't want to see
          scalacOptions ~= (_.filterNot(
              Set("-deprecation", "-unchecked", "-feature") contains _)),

          // Do not generate .class files
          scalacOptions += "-Yskip:cleanup,icode,jvm",

          unmanagedSourceDirectories in Compile := {
            val base = baseDirectory.value
            val ver = scalaVersion.value.substring(0, 4)
            Seq(
                base / s"source-$ver" / "src" / "library",
                base / s"source-$ver" / "src" / "continuations" / "library",
                base / "overrides",
                base / s"overrides-$ver"
            )
          },

          // Exclude files in src/library/ that are overridden in overrides/
          excludeFilter in (Compile, unmanagedSources) := {
            def normPath(f: File): String =
              f.getPath.replace(java.io.File.separator, "/")

            val ver = scalaVersion.value.substring(0, 4)
            val overridesDirs = Seq(
                baseDirectory.value / "overrides",
                baseDirectory.value / s"overrides-$ver"
            )
            val overrideNames = overridesDirs flatMap { overridesDir =>
              val allOverrides = (overridesDir ** "*.scala").get
              val overridePathLen = normPath(overridesDir).length
              val scalaNames =
                for (f <- allOverrides)
                  yield normPath(f).substring(overridePathLen)
              val javaNames =
                for (name <- scalaNames)
                  yield name.substring(0, name.length-6) + ".java"
              scalaNames ++ javaNames
            }
            val libraryPath = normPath(baseDirectory.value / s"source-$ver/src")

            val superFilter = (excludeFilter in (Compile, unmanagedSources)).value
            superFilter || new SimpleFileFilter({ f =>
              val path = normPath(f)
              (
                  // overrides
                  path.startsWith(libraryPath) &&
                  overrideNames.exists(path.endsWith(_))
              ) || (
                  // useless things
                  path.contains("/scala/collection/parallel/") ||
                  path.contains("/scala/util/parsing/")
              )
            })
          },

          // Continuation plugin
          autoCompilerPlugins := true,
          libraryDependencies ++= (
            if (scalaVersion.value startsWith "2.11.") Seq(
              compilerPlugin("org.scala-lang.plugins" %% "scala-continuations-plugin" % "1.0.0-RC3"),
              "org.scala-lang.plugins" %% "scala-continuations-library" % "1.0.0-RC3"
            )
            else Seq(
              compilerPlugin("org.scala-lang.plugins" % "continuations" % scalaVersion.value)
            )
          ),
          scalacOptions += "-P:continuations:enable"
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).dependsOn(compiler % "plugin", library)

  lazy val libraryAux: Project = Project(
      id = "scalajs-library-aux",
      base = file("library-aux"),
      settings = defaultSettings ++ myScalaJSSettings ++ Seq(
          name := "Scala.js aux library",
          publishArtifact in Compile := false,
          delambdafySetting,
          scalacOptions += "-Yskip:cleanup,icode,jvm"
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).dependsOn(compiler % "plugin", library)

  lazy val library: Project = Project(
      id = "scalajs-library",
      base = file("library"),
      settings = defaultSettings ++ publishSettings ++ myScalaJSSettings ++ Seq(
          name := "Scala.js library",
          delambdafySetting
      ) ++ (
          scalaJSExternalCompileSettings
      ) ++ inConfig(Compile)(Seq(
          /* Add the .js and .js.map files from other lib projects
           * (but not .jstype files)
           */
          mappings in packageBin ++= {
            val allProducts = (
                (products in javalib).value ++
                (products in scalalib).value ++
                (products in libraryAux).value)
            val filter = ("*.js": NameFilter) | "*.js.map"
            allProducts.flatMap(dir => (dir ** filter) x relativeTo(dir))
          },

          // Add the core JS library
          mappings in packageBin +=
            (packageJS in corejslib).value.head -> "scalajs-corejslib.js"
      ))
  ).dependsOn(compiler % "plugin")

  // Test framework

  lazy val jasmineTestFramework = Project(
      id = "scalajs-jasmine-test-framework",
      base = file("jasmine-test-framework"),
      settings = defaultSettings ++ publishSettings ++ myScalaJSSettings ++ Seq(
          name := "Scala.js jasmine test framework",

          libraryDependencies ++= Seq(
            "org.webjars" % "jasmine" % "1.3.1"
          )
      )
  ).dependsOn(compiler % "plugin", library)

  // Utils

  /* Dirty trick to add our Scala.js library on the classpath without adding a
   * dependency between projects. This avoids to recompile the library every
   * time we make a change in the compiler, and we want to test it on an
   * example or with the test suite.
   */
  def useProjectButDoNotDependOnIt(project: Project, config: Configuration) = (
      unmanagedClasspath in config += {
        val libraryJar = (artifactPath in (project, Compile, packageBin)).value
        Attributed.blank(libraryJar)
      })

  def useLibraryButDoNotDependOnIt = Seq(
      useProjectButDoNotDependOnIt(library, Compile),
      useProjectButDoNotDependOnIt(library, Test)
  )

  def useJasmineTestFrameworkButDoNotDependOnIt = Seq(
      useProjectButDoNotDependOnIt(jasmineTestFramework, Test),
      libraryDependencies ++=
        (libraryDependencies in jasmineTestFramework).value map (_ % "test")
  )

  // Examples

  lazy val examples: Project = Project(
      id = "examples",
      base = file("examples"),
      settings = defaultSettings ++ Seq(
          name := "Scala.js examples"
      )
  ).aggregate(exampleHelloWorld, exampleReversi)

  lazy val exampleSettings = defaultSettings ++ myScalaJSSettings ++ (
      useLibraryButDoNotDependOnIt ++
      useJasmineTestFrameworkButDoNotDependOnIt
  ) ++ Seq(
      // Add the startup.js file of this example project
      unmanagedSources in (Compile, packageJS) +=
        baseDirectory.value / "startup.js"
  )

  lazy val exampleHelloWorld = Project(
      id = "helloworld",
      base = file("examples") / "helloworld",
      settings = exampleSettings ++ Seq(
          name := "Hello World - Scala.js example",
          moduleName := "helloworld"
      )
  ).dependsOn(compiler % "plugin")

  lazy val exampleReversi = Project(
      id = "reversi",
      base = file("examples") / "reversi",
      settings = exampleSettings ++ Seq(
          name := "Reversi - Scala.js example",
          moduleName := "reversi"
      )
  ).dependsOn(compiler % "plugin")

  lazy val exampleTesting = Project(
      id = "testing",
      base = file("examples") / "testing",
      settings = exampleSettings ++ Seq(
          name := "Testing - Scala.js example",
          moduleName := "testing",

          libraryDependencies ++= Seq(
            "org.webjars" % "jquery" % "1.10.2" % "test",
            "org.webjars" % "envjs" % "1.2" % "test"
          )
      )
  ).dependsOn(compiler % "plugin")

  // Testing

  lazy val test: Project = Project(
      id = "scalajs-test",
      base = file("test"),
      settings = defaultSettings ++ myScalaJSSettings ++ (
          useLibraryButDoNotDependOnIt ++
          useJasmineTestFrameworkButDoNotDependOnIt
      ) ++ Seq(
          name := "Scala.js test suite",
          publishArtifact in Compile := false
      )
  ).dependsOn(compiler % "plugin")

  lazy val partest: Project = Project(
      id = "scalajs-partest",
      base = file("partest"),
      settings = defaultSettings ++ Seq(
        name := "Partest for Scala.js",
        moduleName := "scalajs-partest",
        crossScalaVersions := Seq("2.11.0-M8"), // no partest on 2.10
        resolvers += Resolver.typesafeIvyRepo("releases"),
        libraryDependencies ++= Seq(
            "org.scala-sbt" % "sbt" % "0.13.1",
            "com.google.javascript" % "closure-compiler" % "v20130603",
            "org.mozilla" % "rhino" % "1.7R4"
        ),
        libraryDependencies ++= (if (scalaVersion.value startsWith "2.10.") Nil else Seq("org.scala-lang.modules" %% "scala-partest" % "1.0.0-RC8")),
        unmanagedSourceDirectories in Compile ++= {
          val base = ((scalaSource in (plugin, Compile)).value /
              "scala/scalajs/sbtplugin")
          Seq(base / "environment", base / "sourcemap")
        },
        sources in Compile += (
            (scalaSource in (plugin, Compile)).value /
            "scala/scalajs/sbtplugin/ScalaJSEnvironment.scala")
      )
  ).dependsOn(compiler)

  lazy val partestSuite: Project = Project(
      id = "scalajs-partest-suite",
      base = file("partest-suite"),
      settings = defaultSettings ++ (
          useLibraryButDoNotDependOnIt
      ) ++ Seq(
          name := "Scala.js partest suite",
          crossScalaVersions := Seq("2.11.0-M8"), // no partest on 2.10

          /* Add an extracted version of scalajs-library.jar on the classpath.
           * The runner will need it, as it cannot cope with .js files in .jar.
           */
          dependencyClasspath in Test += {
            val s = streams.value

            val taskCacheDir = s.cacheDirectory / "extract-scalajs-library"
            val extractDir = taskCacheDir / "scalajs-library"

            val libraryJar =
              (artifactPath in (library, Compile, packageBin)).value

            val cachedExtractJar = FileFunction.cached(taskCacheDir / "cache-info",
                FilesInfo.lastModified, FilesInfo.exists) { dependencies =>

              val usefulFilesFilter = ("*.js": NameFilter) | ("*.js.map")
              s.log.info("Extracting %s ..." format libraryJar)
              if (extractDir.exists)
                IO.delete(extractDir)
              IO.createDirectory(extractDir)
              IO.unzip(libraryJar, extractDir, filter = usefulFilesFilter,
                  preserveLastModified = true)
              (extractDir ** usefulFilesFilter).get.toSet
            }

            cachedExtractJar(Set(libraryJar))

            Attributed.blank(extractDir)
          },

          fork in Test := true,
          javaOptions in Test += "-Xmx1G",
          //Uncomment what you need here
          //javaOptions in Test += "-Dscala.tools.partest.scalajs.testunknownonly=true",
          //javaOptions in Test += "-Dscala.tools.partest.scalajs.useblacklist=true",
          //javaOptions in Test += "-Dscala.tools.partest.scalajs.testblackbugonly=true",

          testFrameworks +=
            new TestFramework("scala.tools.partest.scalajs.Framework"),

          definedTests in Test +=
            new sbt.TestDefinition(
                "partest",
                // marker fingerprint since there are no test classes
                // to be discovered by sbt:
                new sbt.testing.AnnotatedFingerprint {
                  def isModule = true
                  def annotationName = "partest"
                },
                true,
                Array()
            )
      )
  ).dependsOn(partest % "test")
}
