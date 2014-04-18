package scala.tools.nsc

/* Super hacky overriding of the MainGenericRunner used by partest */

import scala.scalajs.tools.classpath._
import scala.scalajs.tools.logging._
import scala.scalajs.tools.io._
import scala.scalajs.tools.optimizer.ScalaJSOptimizer
import scala.scalajs.tools.env.JSConsole

import scala.scalajs.sbtplugin.env.rhino.RhinoJSEnv
import scala.scalajs.sbtplugin.env.nodejs.NodeJSEnv
import scala.scalajs.sbtplugin.JSUtils._

import java.io.File
import Properties.{ versionString, copyrightString }
import GenericRunnerCommand._

class ScalaConsoleLogger extends Logger {
  def log(level: Level, message: =>String): Unit = {
    if (level == Level.Warn || level == Level.Error)
      scala.Console.err.println(message)
    else
      scala.Console.out.println(message)
  }
  def success(message: => String): Unit = info(message)
  def trace(t: => Throwable): Unit = t.printStackTrace()
}

class ScalaConsoleJSConsole extends JSConsole {
  def log(msg: Any) = scala.Console.out.println(msg.toString)
}

class MainGenericRunner {
  def errorFn(ex: Throwable): Boolean = {
    ex.printStackTrace()
    false
  }
  def errorFn(str: String): Boolean = {
    scala.Console.err println str
    false
  }

  val optimize = sys.props.contains("scalajs.partest.optimize")

  def process(args: Array[String]): Boolean = {
    val command = new GenericRunnerCommand(args.toList, (x: String) => errorFn(x))
    import command.{ settings, howToRun, thingToRun }

    if (!command.ok) return errorFn("\n" + command.shortUsageMsg)
    else if (settings.version) return errorFn("Scala code runner %s -- %s".format(versionString, copyrightString))
    else if (command.shouldStopWithInfo) return errorFn("shouldStopWithInfo")

    if (howToRun != AsObject)
      return errorFn("Scala.js runner can only run an object")

    val usefulClasspathEntries = for {
      url <- settings.classpathURLs
      f = urlToFile(url)
      if (f.isDirectory || f.getName.startsWith("scalajs-library"))
    } yield f
    val classpath = ScalaJSClasspath.fromClasspath(usefulClasspathEntries)

    val logger = new ScalaConsoleLogger
    val jsConsole = new ScalaConsoleJSConsole

    val (runnerFile, reachability) =
      runnerJSFile(thingToRun, command.arguments)

    if (optimize) {
      import ScalaJSOptimizer._

      val optimizer = new ScalaJSOptimizer
      val objName = thingToRun.replace('.', '_')

      val fileName = "partest optimized file"
      val packFileWriter = new MemVirtualScalaJSPackfileWriter

      try {
        optimizer.optimize(
            Inputs(classpath, manuallyReachable = reachability),
            OutputConfig(
                name          = fileName,
                writer        = packFileWriter,
                wantSourceMap = false
                ),
            logger
        )
      } finally {
        packFileWriter.close()
      }

      val packFile = packFileWriter.toVirtualFile(fileName)
      val packedClasspath = ScalaJSPackedClasspath(Seq(packFile), Nil)
      val env = new NodeJSEnv
      env.runJS(packedClasspath, runnerFile, logger, jsConsole)
    } else {
      val env = new RhinoJSEnv
      env.runJS(classpath, runnerFile, logger, jsConsole)
    }

    true
  }

  private def runnerJSFile(mainObj: String, args: List[String]) = {
    import ScalaJSOptimizer._

    val mainModule = mainObj.replace('.', '_')
    val mainModule_main = "main__AT__V"

    val mainReach = Seq(
      ReachObject(mainModule),
      ReachMethod(mainModule + '$', mainModule_main, static = false))

    val (jsArgs, argReach) = toScalaStringArray(listToJS(args))

    val vFile = new MemVirtualJSFile("Generated launcher file").
      withContent(s"${mod(mainModule)}.$mainModule_main($jsArgs);")

    (vFile, mainReach ++ argReach)
  }

  /** constructs js.Any.toArray($jsArr)(ClassTag(classOf[String])) */
  private def toScalaStringArray(jsArr: String) = {
    import ScalaJSOptimizer._

    val jsAnyModule = "scala_scalajs_js_Any"
    val jsAny_toArray = "toArray__Lscala_scalajs_js_Array__Lscala_reflect_ClassTag__O"

    val ClassTagModule = "scala_reflect_ClassTag"
    val ClassTag_apply = "apply__Ljava_lang_Class__Lscala_reflect_ClassTag"
    
    val StringClass = "java_lang_String"

    val reach = Seq(
      ReachObject(jsAnyModule),
      ReachMethod(jsAnyModule + '$', jsAny_toArray, static = false),
      ReachObject(ClassTagModule),
      ReachMethod(ClassTagModule + '$', ClassTag_apply, static = false),
      ReachData(StringClass)
    )

    val code = s"""${mod(jsAnyModule)}.$jsAny_toArray($jsArr,
      ${mod(ClassTagModule)}.$ClassTag_apply(${data(StringClass)}.getClassOf()))"""

    (code, reach)
  }

  /** generate module accessor for a module name */
  private def mod(name: String): String = s"ScalaJS.modules.$name()" 

  /** generate data accessor for a class name */
  private def data(name: String): String = s"ScalaJS.data.$name" 

  private def urlToFile(url: java.net.URL) = {
    try {
      new File(url.toURI())
    } catch {
      case e: java.net.URISyntaxException => new File(url.getPath())
    }
  }
}

object MainGenericRunner extends MainGenericRunner {
  def main(args: Array[String]) {
    if (!process(args))
      sys.exit(1)
  }
}
