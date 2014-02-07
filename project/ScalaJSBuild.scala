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
    /* Friendly error message when we forget to fetch the submodule
     * or when we forget to update it after changing branch. */
    {
      val f = (s: State) => {
        val logger = s.globalLogging.full
        import logger.warn
        val base = s.configuration.baseDirectory()
        val scalalibHeadFile = base / ".git/modules/scalalib/source/HEAD"
        if (!scalalibHeadFile.exists()) {
          warn("It seems you have not fetched the scalalib/source submodule.")
          warn("This will prevent you from building Scala.js!")
          warn("You can fix this by doing the following:")
          warn("  $ git submodule init")
          warn("  $ git submodule update")
        } else {
          val sha = IO.readLines(scalalibHeadFile).headOption
          if (sha != Some("60d462ef6e0dba5f9a7c4cc81255fcb9fba7939a")) {
            warn("The head of the scala/source submodule is not the one I expected.")
            warn("This will likely prevent you from building Scala.js and will cause weird errors!")
            warn("You can fix this by doing the following:")
            warn("  $ git submodule update")
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
              // compiler, plugin, library and jasmineTestFramework are aggregated
              clean in corejslib, clean in javalib, clean in scalalib,
              clean in libraryAux, clean in test, clean in examples,
              clean in exampleHelloWorld, clean in exampleReversi,
              clean in exampleTesting).value,

          publish := {},
          publishLocal := {}
      )
  ).aggregate(
      compiler, plugin, library, jasmineTestFramework
  )

  lazy val compiler: Project = Project(
      id = "scalajs-compiler",
      base = file("compiler"),
      settings = defaultSettings ++ publishSettings ++ Seq(
          name := "Scala.js compiler",
          libraryDependencies ++= Seq(
              "org.scala-lang" % "scala-compiler" % scalaJSScalaVersion,
              "org.scala-lang" % "scala-reflect" % scalaJSScalaVersion
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

  lazy val javalib: Project = Project(
      id = "scalajs-javalib",
      base = file("javalib"),
      settings = defaultSettings ++ myScalaJSSettings ++ Seq(
          name := "Java library for Scala.js",
          publishArtifact in Compile := false,
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

          // The Scala lib is full of warnings we don't want to see
          scalacOptions ~= (_.filterNot(
              Set("-deprecation", "-unchecked", "-feature") contains _)),

          // Do not generate .class files
          scalacOptions += "-Yskip:cleanup,icode,jvm",

          // Exclude files that are overridden in library
          excludeFilter in (Compile, unmanagedSources) ~= { superFilter =>
            superFilter || new SimpleFileFilter({ f =>
              val path = f.getPath.replace(java.io.File.separator, "/")
              (path.endsWith("/scala/package.scala")
                  || path.endsWith("/scala/App.scala")
                  || path.endsWith("/scala/Console.scala")
                  || path.endsWith("/scala/compat/Platform.scala")
                  || path.endsWith("/scala/runtime/BoxesRunTime.scala")
                  || path.endsWith("/scala/util/control/NoStackTrace.scala")

                  // Hideous but effective way not to compile useless parts
                  || path.contains("/scala/collection/parallel/")
                  || path.contains("/scala/util/parsing/"))
            })
          },

          // Continuation plugin
          autoCompilerPlugins := true,
          libraryDependencies += compilerPlugin(
              "org.scala-lang.plugins" % "continuations" % scalaVersion.value),
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
          scalacOptions += "-Yskip:cleanup,icode,jvm"
      ) ++ (
          scalaJSExternalCompileSettings
      )
  ).dependsOn(compiler % "plugin", library)

  lazy val library: Project = Project(
      id = "scalajs-library",
      base = file("library"),
      settings = defaultSettings ++ publishSettings ++ myScalaJSSettings ++ Seq(
          name := "Scala.js library"
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

}
