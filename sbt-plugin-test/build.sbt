import scala.concurrent.Await
import scala.concurrent.duration.Duration

import org.scalajs.io._
import org.scalajs.linker._
import org.scalajs.sbtplugin.Loggers.sbtLogger2ToolsLogger
import org.scalajs.sbtplugin.ScalaJSCrossVersion

lazy val concurrentFakeFullOptJS = taskKey[Any]("")
lazy val concurrentUseOfLinkerTest = taskKey[Any]("")

name := "Scala.js sbt test"

version := scalaJSVersion

val versionSettings = Seq(
  version := scalaJSVersion,
  scalaVersion := "2.11.12"
)

val baseSettings = versionSettings ++ Seq(
  testOptions += Tests.Argument(
    TestFramework("com.novocode.junit.JUnitFramework"), "-v", "-a", "-s"),

  // Test that non-existent classpath entries are allowed - #2198
  fullClasspath in Compile += (baseDirectory in LocalProject("root")).value /
    "non-existent-directory-please-dont-ever-create-this"
)

val testScalaJSSourceMapAttribute = TaskKey[Unit](
  "testScalaJSSourceMapAttribute", "", KeyRanks.BTask)

val testScalaJSModuleInitializers = TaskKey[Unit](
  "testScalaJSModuleInitializers", "", KeyRanks.BTask)

lazy val root = project.in(file(".")).
  aggregate(noDOM, multiTestJS, multiTestJVM)

lazy val noDOM = project.settings(baseSettings: _*).
  enablePlugins(ScalaJSPlugin).
  enablePlugins(ScalaJSJUnitPlugin).
  settings(
    name := "Scala.js sbt test w/o DOM",
    scalaJSUseMainModuleInitializer := true,
    scalaJSModuleInitializers +=
      ModuleInitializer.mainMethod("sbttest.noDOM.TestApp", "foo"),
    scalaJSModuleInitializers in Test +=
      ModuleInitializer.mainMethod("sbttest.noDOM.InitHolder", "foo"),

    testScalaJSModuleInitializers := {
      // Compile should have main module init and TestApp.foo
      assert((scalaJSModuleInitializers in Compile).value.size == 2,
        "Bad number of scalaJSModuleInitializers in Compile")

      // Test should have test module init, InitHolder.foo and TestApp.foo
      assert((scalaJSModuleInitializers in Test).value.size == 3,
        "Bad number of scalaJSModuleInitializers in Test")
    }
  ).
  /* This hopefully exposes concurrent uses of the linker. If it fails/gets
   * flaky, there is a bug somewhere - #2202
   */
  settings(inConfig(Compile)(Seq(
      // A fake fullOptJS that we will run concurrently with the true fullOptJS
      concurrentFakeFullOptJS := Def.taskDyn {
        val s = (streams in fullOptJS).value
        val log = s.log
        val ir = (scalaJSIR in fullOptJS).value.data
        val moduleInitializers = scalaJSModuleInitializers.value

        Def.task {
          import scala.concurrent.ExecutionContext.Implicits.global

          log.info("Fake full optimizing")
          val linker = (scalaJSLinker in fullOptJS).value
          val output = LinkerOutput(new WritableMemVirtualBinaryFile)
          Await.result(
              linker.link(ir, moduleInitializers, output, sbtLogger2ToolsLogger(log)),
              Duration.Inf)
        }.tag((usesScalaJSLinkerTag in fullOptJS).value)
      }.value,

      /* Depend on both fullOptJS and concurrentFakeFullOptJS, so that they
       * are hopefully executed in parallel (potentially, but they should be
       * blocked from actually doing so by the concurrent restrictions on
       * usesScalaJSLinkerTag).
       */
      concurrentUseOfLinkerTest := {
        (fullOptJS.value, concurrentFakeFullOptJS.value)
      }
  )))

lazy val testFrameworkCommonSettings = Def.settings(
  versionSettings,
  name := "Dummy cross JS/JVM test framework",
  unmanagedSourceDirectories in Compile +=
    baseDirectory.value.getParentFile / "shared/src/main/scala"
)

lazy val testFrameworkJS = project.in(file("testFramework/js")).
  enablePlugins(ScalaJSPlugin).
  settings(
    testFrameworkCommonSettings,
    libraryDependencies +=
      "org.scala-js" %% "scalajs-test-interface" % scalaJSVersion
  )

lazy val testFrameworkJVM = project.in(file("testFramework/jvm")).
  settings(
    testFrameworkCommonSettings,
    libraryDependencies ++= Seq(
        "org.scala-sbt" % "test-interface" % "1.0"
    )
  )

lazy val multiTestCommonSettings = Def.settings(
  unmanagedSourceDirectories in Compile +=
    baseDirectory.value.getParentFile / "shared/src/main/scala",
  unmanagedSourceDirectories in Test +=
    baseDirectory.value.getParentFile / "shared/src/test/scala",

  testFrameworks ++= Seq(
      TestFramework("sbttest.framework.DummyFramework"),
      TestFramework("inexistent.Foo", "another.strange.Bar")
  )
)

lazy val multiTestJS = project.in(file("multiTest/js")).
  enablePlugins(ScalaJSJUnitPlugin).
  settings(multiTestCommonSettings).
  settings(baseSettings: _*).
  settings(
    name := "Multi test framework test JS",

    // Test platformDepsCrossVersion (as a setting, it's evaluated when loading the build)
    platformDepsCrossVersion ~= { value =>
      assert(value eq ScalaJSCrossVersion.binary,
          "platformDepsCrossVersion should be ScalaJSCrossVersion.binary in multiTestJS")
      value
    },

    // Test the scalaJSSourceMap attribute of fastOptJS and fullOptJS
    testScalaJSSourceMapAttribute in Test := {
      val fastOptFile = (fastOptJS in Test).value
      assert(fastOptFile.get(scalaJSSourceMap).exists {
        _.getPath == fastOptFile.data.getPath + ".map"
      }, "fastOptJS does not have the correct scalaJSSourceMap attribute")

      val fullOptFile = (fullOptJS in Test).value
      assert(fullOptFile.get(scalaJSSourceMap).exists {
        _.getPath == fullOptFile.data.getPath + ".map"
      }, "fullOptJS does not have the correct scalaJSSourceMap attribute")
    }
  ).
  dependsOn(testFrameworkJS % "test")

lazy val multiTestJVM = project.in(file("multiTest/jvm")).
  settings(multiTestCommonSettings).
  settings(versionSettings: _*).
  settings(
    name := "Multi test framework test JVM",
    libraryDependencies +=
      "com.novocode" % "junit-interface" % "0.9" % "test",

    // Test platformDepsCrossVersion (as a setting, it's evaluated when loading the build)
    platformDepsCrossVersion := {
      val value = platformDepsCrossVersion.value
      if (!sbtVersion.value.startsWith("0.")) {
        // In 0.13, CrossVersions do not have a meaningful ==, but they do in 1.0
        assert(value == CrossVersion.binary,
            "platformDepsCrossVersion should be CrossVersion.binary in multiTestJVM")
      }
      value
    }
  ).
  dependsOn(testFrameworkJVM % "test")
