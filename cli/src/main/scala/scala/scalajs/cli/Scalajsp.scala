/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js CLI               **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013-2014, LAMP/EPFL   **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package scala.scalajs.cli

import scala.scalajs.ir
import ir.ScalaJSVersions
import ir.Trees.{Tree, ClassDef}
import ir.JSDesugaring.desugarJavaScript
import ir.Printers.{InfoPrinter, IRTreePrinter}

import scala.scalajs.tools.io._
import scala.collection.immutable.Seq

import java.io.{Console => _, _}
import java.util.zip.{ZipFile, ZipEntry}

object Scalajsp {

  case class Options(
    infos: Boolean = false,
    desugar: Boolean = false,
    showReflProxy: Boolean = false,
    jar: Option[File] = None,
    fileNames: Seq[String] = Seq.empty)

  def main(args: Array[String]): Unit = {
    val parser = new scopt.OptionParser[Options]("scalajsp") {
      head("scalajsp", ScalaJSVersions.current)
      arg[String]("<file> ...")
        .unbounded()
        .action { (x, c) => c.copy(fileNames = c.fileNames :+ x) }
        .text("*.sjsir file to display content of")
      opt[File]('j', "jar")
        .valueName("<jar>")
        .action { (x, c) => c.copy(jar = Some(x)) }
        .text("Read *.sjsir file(s) from the given JAR.")
      opt[Unit]('d', "desugar")
        .action { (_, c) => c.copy(desugar = true) }
        .text("Desugar JS trees. This yields runnable JavaScript")
      opt[Unit]('i', "infos")
        .action { (_, c) => c.copy(infos = true) }
        .text("Show DCE infos instead of trees")
      opt[Unit]('p', "reflProxies")
        .action { (_, c) => c.copy(showReflProxy = true) }
        .text("Show reflective call proxies")
      opt[Unit]('s', "supported")
        .action { (_,_) => printSupported(); sys.exit() }
        .text("Show supported Scala.js IR versions")
      version("version")
        .abbr("v")
        .text("Show scalajsp version")
      help("help")
        .abbr("h")
        .text("prints this usage text")

      override def showUsageOnError = true
    }

    for {
      options  <- parser.parse(args, Options())
      fileName <- options.fileNames
    } {
      val vfile = options.jar map { jar =>
        readFromJar(jar, fileName)
      } getOrElse {
        readFromFile(fileName)
      }

      displayFileContent(vfile, options)
    }
  }

  def printSupported(): Unit = {
    import ScalaJSVersions._
    println(s"Emitted Scala.js IR version is: $binaryEmitted")
    println("Supported Scala.js IR versions are")
    binarySupported.foreach(v => println(s"* $v"))
  }

  def displayFileContent(vfile: VirtualScalaJSIRFile, opts: Options): Unit = {
    if (opts.infos)
      new InfoPrinter(stdout).printClassInfo(vfile.info)
    else {
      val outTree = {
        if (opts.showReflProxy) vfile.tree
        else filterOutReflProxies(vfile.tree)
      }

      if (opts.desugar)
        new IRTreePrinter(stdout, jsMode = true).printTopLevelTree(
          desugarJavaScript(outTree))
      else
        new IRTreePrinter(stdout, jsMode = false).printTopLevelTree(outTree)
    }

    stdout.flush()
  }

  private def fail(msg: String) = {
    Console.err.println(msg)
    sys.exit(1)
  }

  private def readFromFile(fileName: String) = {
    val file = new File(fileName)

    if (!file.exists)
      fail(s"No such file: $fileName")
    else if (!file.canRead)
      fail(s"Unable to read file: $fileName")
    else
      FileVirtualScalaJSIRFile(file)
  }

  private def readFromJar(jar: File, name: String) = {
    val jarFile =
      try { new ZipFile(jar) }
      catch { case _: FileNotFoundException => fail(s"No such JAR: $jar") }
    try {
      val entry = jarFile.getEntry(name)
      if (entry == null)
        fail(s"No such file in jar: $name")
      else {
        val name = jarFile.getName + "#" + entry.getName
        val content =
          IO.readInputStreamToByteArray(jarFile.getInputStream(entry))
        new MemVirtualSerializedScalaJSIRFile(name).withContent(content)
      }
    } finally {
      jarFile.close()
    }
  }

  private val stdout =
    new BufferedWriter(new OutputStreamWriter(Console.out, "UTF-8"))

  private def filterOutReflProxies(tree: ClassDef): ClassDef = {
    import ir.Trees._
    import ir.Definitions.isReflProxyName
    val newDefs = tree.defs.filter {
      case MethodDef(Ident(name, _), _, _, _) => !isReflProxyName(name)
      case _ => true
    }
    tree.copy(defs = newDefs)(tree.pos)
  }

}
