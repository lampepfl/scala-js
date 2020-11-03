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

package org.scalajs.linker.frontend.modulesplitter

import scala.collection.immutable
import scala.collection.mutable

import org.scalajs.ir.Names.ClassName
import org.scalajs.linker.standard.ModuleSet.ModuleID

/** Build fewest (largest) possible modules (without reaching unnecessary code).
 *
 *  Calculates a transitive closure over the dependency graph for each public
 *  module. After that, each class ends up with set of "tags": one "tag" for
 *  each public module it can be reached by. We then create a module for each
 *  distinct set of tags.
 */
private[modulesplitter] final class MaxModuleAnalyzer extends ModuleAnalyzer {
  import MaxModuleAnalyzer._

  def analyze(info: ModuleAnalyzer.DependencyInfo): ModuleAnalyzer.Analysis = {
    if (info.publicModuleDependencies.size == 1) {
      // Fast path.
      new SingleModuleAnalysis(info.publicModuleDependencies.head._1)
    } else {
      new Run(info).analyze()
    }
  }
}

private object MaxModuleAnalyzer {

  private final class SingleModuleAnalysis(moduleID: ModuleID) extends ModuleAnalyzer.Analysis {
    def moduleForClass(className: ClassName): Option[ModuleID] =
      Some(moduleID)
  }

  private final class FullAnalysis(map: Map[ClassName, ModuleID]) extends ModuleAnalyzer.Analysis {
    def moduleForClass(className: ClassName): Option[ModuleID] =
      map.get(className)
  }

  private final class Run(infos: ModuleAnalyzer.DependencyInfo) {
    private[this] val allTags =
      mutable.Map.empty[ClassName, mutable.Set[ModuleID]]

    def analyze(): ModuleAnalyzer.Analysis = {
      tagEntryPoints()

      val moduleIDs = buildModuleIDs()

      val moduleMap = allTags.map { case (className, tags) =>
        className -> moduleIDs(tags)
      }.toMap

      new FullAnalysis(moduleMap)
    }

    private def tag(className: ClassName, moduleID: ModuleID): Unit = {
      val perClassTags = allTags.getOrElseUpdate(className, mutable.Set.empty)
      if (perClassTags.add(moduleID))
        infos.classDependencies(className).foreach(tag(_, moduleID))
    }

    private def tagEntryPoints(): Unit = {
      for {
        (moduleID, deps) <- infos.publicModuleDependencies
        className <- deps
      } {
        tag(className, moduleID)
      }
    }

    private def buildModuleIDs(): Map[scala.collection.Set[ModuleID], ModuleID] = {
      /* We build the new module IDs independent of the actually present
       * modules to ensure stability.
       *
       * We sort the ModuleIDs to not depend on map iteration order (or the
       * order of the input files).
       *
       * All of this is to avoid module ID collisions, for example with the
       * following set of public modules: {`a`, `b`, `a-b`}.
       */
      val publicIDs = {
        // Best way I could find to create SortedSet from a Set :-/
        val b = immutable.SortedSet.newBuilder(Ordering.by[ModuleID, String](_.id))
        infos.publicModuleDependencies.keysIterator.foreach(b += _)
        b.result()
      }

      val seenIDs = mutable.Set.empty[ModuleID]

      val tups = for {
        modules <- publicIDs.subsets()
        if modules.nonEmpty
      } yield {
        var candidate = ModuleID(modules.map(_.id).mkString("-"))

        while (seenIDs.contains(candidate))
          candidate = ModuleID(candidate.id + "$")

        seenIDs.add(candidate)

        modules -> candidate
      }

      tups.toMap
    }
  }
}
