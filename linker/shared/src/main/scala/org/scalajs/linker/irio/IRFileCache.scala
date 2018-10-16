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

package org.scalajs.linker.irio

import scala.annotation.tailrec

import java.net.URI

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

import org.scalajs.ir.EntryPointsInfo
import org.scalajs.ir.Trees.ClassDef

import org.scalajs.io._

/** Centralized Scala.js IR cache.
 *
 *  Caches all Scala.js IR used in a given JVM. It supports creating of multiple
 *  sub-caches ([[IRFileCache.Cache]]) that track individual file sets.
 *  The global cache is fully thread-safe. However, the sub-caches are not.
 */
final class IRFileCache {
  /* General implementation comment: We always synchronize before doing I/O
   * (instead of using a calculate and CAS pattern). This is since we assume
   * that paying the cost for synchronization is lower than I/O.
   */

  import IRFileCache._

  /** Holds the cached IR */
  private[this] val globalCache = new ConcurrentHashMap[String, PersistedFiles]

  // Statistics
  private[this] val statsReused = new AtomicInteger(0)
  private[this] val statsInvalidated = new AtomicInteger(0)
  private[this] val statsTreesRead = new AtomicInteger(0)

  /** Create a new sub-cache.
   *
   *  Users should call [[IRFileCache.Cache.free]] once they are done to allow
   *  for more aggressive GC.
   */
  def newCache: Cache = new CacheImpl

  /** Approximate statistics about the cache usage */
  def stats: IRFileCache.Stats = {
    new IRFileCache.Stats(statsReused.get, statsInvalidated.get,
        statsTreesRead.get)
  }

  /** Reset statistics */
  def clearStats(): Unit = {
    statsReused.set(0)
    statsInvalidated.set(0)
    statsTreesRead.set(0)
  }

  private final class CacheImpl extends Cache {
    private[this] var localCache: Seq[PersistedFiles] = _

    def cached(files: Seq[ScalaJSIRContainer]): Seq[VirtualScalaJSIRFile] = {
      update(files)
      localCache.flatMap(_.files)
    }

    private def update(files: Seq[ScalaJSIRContainer]): Unit = clearOnThrow {
      val result = Seq.newBuilder[PersistedFiles]

      for (file <- files) {
        @tailrec
        def putContents(): PersistedFiles = {
          val newValue = new PersistedFiles(file.path)
          val oldValue = globalCache.putIfAbsent(file.path, newValue)

          val contents = if (oldValue != null) oldValue else newValue

          if (contents.reference()) contents
          else putContents()
        }

        val contents = putContents()
        contents.update(file)
        result += contents
      }

      free()
      localCache = result.result()
    }

    def free(): Unit = {
      if (localCache != null) {
        localCache.foreach(_.unreference())
        localCache = null
      }
    }

    protected override def finalize(): Unit = {
      free()
    }
  }

  /** Stores the extracted [[VirtualScalaJSIRFile]]s from the file at path.
   *
   *  This also tracks references to itself by reference counting.
   *  Further, a [[PersistedFiles]] has a tombstone state. It is necessary to
   *  avoid a race between referencing a file just retrieved from
   *  [[globalCache]] and removing a file from [[globalCache]] that has just
   *  been unreferenced.
   */
  private final class PersistedFiles(path: String) {

    /** Number of references we have. -1 means we are a tombstone */
    private[this] val _references = new AtomicInteger(0)

    /** Last version we have been updated with.
     *  May only be written under synchronization, except if this is a tombstone
     */
    @volatile
    private[this] var _version: Option[String] = None

    /** Files in this [[PersistedFiles]]
     *  May only be written under synchronization, except if this is a tombstone
     */
    @volatile
    private[this] var _files: Seq[VirtualScalaJSIRFile] = null

    def files: Seq[VirtualScalaJSIRFile] = _files

    /** Try to reference this block of files.
     *  @return true if referencing succeeded, false if this is a tombstone
     */
    @tailrec
    final def reference(): Boolean = {
      val refs = _references.get

      if (refs == -1) {
        // we are a tombstone, help cleaning up and bail out
        cleanup()
        false
      } else {
        // try to increase ref count
        if (_references.compareAndSet(refs, refs + 1)) true // done
        else reference() // something changed, try again
      }
    }

    /** Unreference this file.
     *
     *  If there are no references any more, turn this [[PersistedFiles]] into
     *  a tombstone and remove it from the cache.
     */
    final def unreference(): Unit = {
      val refs = _references.decrementAndGet()
      assert(refs >= 0, "Unreferencing an not referenced file")

      /* If we have 0 references, try to become a tombstone. We could be
       * referenced again in a race. In this case, don't do anything.
       */
      if (refs == 0 && _references.compareAndSet(0, -1)) {
        cleanup()
      }
    }

    /** Clean up, after becoming a tombstone */
    private def cleanup(): Unit = {
      /* We need to verify our own identity. Otherwise we might mess with a new,
       * clean state after an exception (if we are pre-exception).
       */
      globalCache.remove(path, this)
      // aggressively free stuff for GC
      _version = null
      _files = null
    }

    /** Updates this file with the given [[ScalaJSIRContainer]].
     *
     *  May only be called by a thread, if it holds a reference to this file.
     */
    def update(file: ScalaJSIRContainer): Unit = {
      assert(_references.get > 0, "Updating an unreferenced file")
      assert(file.path == path, s"Path mismatch: $path, ${file.path}")

      // Helper to ensure v is stable during check
      @inline
      def upToDate(v: Option[String]) = v.isDefined && v == file.version

      if (upToDate(_version)) {
        // yeepeeh, nothing to do
        statsReused.incrementAndGet()
      } else {
        // We need to update this. We synchronize
        synchronized {
          if (upToDate(_version)) {
            // someone else had the same idea and did our work
            statsReused.incrementAndGet()
          } else {
            statsInvalidated.incrementAndGet()
            _files = file.sjsirFiles.map(new PersistentIRFile(_))
            _version = file.version
          }
        }
      }
    }
  }

  private final class PersistentIRFile(
      private[this] var _irFile: VirtualScalaJSIRFile)
      extends VirtualScalaJSIRFile {

    @volatile
    private[this] var _tree: ClassDef = null

    override val path: String = _irFile.path
    override val version: Option[String] = _irFile.version
    override val entryPointsInfo: EntryPointsInfo = _irFile.entryPointsInfo
    override val relativePath: String = _irFile.relativePath

    override def tree: ClassDef = {
      if (_tree == null) {
        synchronized {
          if (_tree == null) { // check again, race!
            loadTree()
          }
        }
      }

      _tree
    }

    /** Must be called under synchronization only */
    private def loadTree(): Unit = clearOnThrow {
      statsTreesRead.incrementAndGet()
      _tree = _irFile.tree // This can fail due to I/O
      _irFile = null // Free for GC
    }
  }

  /** If something fails, we clear the `globalCache` to avoid leaks. The already
   *  existing [[PersistedFiles]]s may continue to exist. This is OK, since in
   *  the worst case they will try to remove themselves form a map in which they
   *  are not anymore.
   */
  @inline
  private def clearOnThrow[T](body: => T): T = {
    try body
    catch {
      case t: Throwable =>
        globalCache.clear()
        throw t
    }
  }

}

object IRFileCache {
  /** A cache to use for individual runs. Not threadsafe */
  sealed trait Cache {
    /** Extract and cache IR.
     *
     *  The returned value is valid until the next invocation of [[cached]] or
     *  [[free]].
     *
     *  @note Updating any of the underlying files in the container during the
     *      lifetime of a returned [[VirtualScalaJSIRFile]] yields
     *      unspecified behavior.
     */
    def cached(files: Seq[ScalaJSIRContainer]): Seq[VirtualScalaJSIRFile]

    /** Should be called if this cache is not used anymore.
     *
     *  Frees resources in the global cache, if they are not used anymore.
     *  The cache may be reused after calling [[free]] (but this is not any
     *  faster than calling [[IRFileCache.newCache]], modulo the object
     *  allocation).
     */
    def free(): Unit
  }

  final class Stats(val reused: Int, val invalidated: Int, val treesRead: Int) {
    /** Descriptive line to display in logs */
    def logLine: String = {
      s"reused: $reused -- " +
      s"invalidated: $invalidated -- " +
      s"trees read: $treesRead"
    }
  }
}
