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

package org.scalajs.linker.backend.emitter

import scala.collection.mutable

import org.scalajs.ir.{ClassKind, Definitions}
import org.scalajs.ir.Trees._
import org.scalajs.ir.Types.Type

import org.scalajs.linker._
import org.scalajs.linker.standard._

private[emitter] final class KnowledgeGuardian {
  import KnowledgeGuardian._

  private var firstRun: Boolean = true

  private var isParentDataAccessed: Boolean = _

  private val classes = mutable.Map.empty[String, Class]

  private def askIsParentDataAccessed(invalidatable: Invalidatable): Boolean =
    isParentDataAccessed

  /** Returns `true` if *all* caches should be invalidated.
   *
   *  For global properties that are rarely changed and heavily used (such as
   *  isParentDataAccessed), we do not want to pay the price of the
   *  dependency graph, in terms of memory consumption and time spent
   *  maintaining it. It is a better trade-off to invalidate everything in
   *  the rare events where they do change.
   */
  def update(linkingUnit: LinkingUnit): Boolean = {
    val hasInlineableInit = computeHasInlineableInit(linkingUnit)

    var newIsParentDataAccessed = false

    // Update classes
    for (linkedClass <- linkingUnit.classDefs) {
      val encodedName = linkedClass.encodedName
      val thisClassHasInlineableInit = hasInlineableInit(encodedName)
      classes.get(encodedName).fold[Unit] {
        // new class
        classes.put(encodedName,
            new Class(linkedClass, thisClassHasInlineableInit))
      } { existingCls =>
        existingCls.update(linkedClass, thisClassHasInlineableInit)
      }

      def methodExists(encodedName: String): Boolean =
        linkedClass.memberMethods.exists(_.value.encodedName == encodedName)

      linkedClass.encodedName match {
        case Definitions.ClassClass =>
          newIsParentDataAccessed = methodExists("getSuperclass__jl_Class")
        case _ =>
      }
    }

    // Garbage collection
    classes.retain((_, cls) => cls.testAndResetIsAlive())

    val invalidateAll = !firstRun && {
      newIsParentDataAccessed != isParentDataAccessed
    }
    firstRun = false

    isParentDataAccessed = newIsParentDataAccessed

    if (invalidateAll)
      classes.valuesIterator.foreach(_.unregisterAll())
    invalidateAll
  }

  private def computeHasInlineableInit(linkingUnit: LinkingUnit): Set[String] = {
    /* Those classes are instantiated in scalajsenv.js. Since they have
     * multiple constructors and/or are not final, scalajsenv.js is written
     * with the assumption that they will not have an inlineable init. We
     * therefore blacklist them here so that this is always true.
     *
     * Note that j.l.Class is not in this list, because it has only one
     * constructor and is final, so even scalajsenv.js can assume it always
     * has an inlineable init.
     */
    val blackList = Set(
        "jl_ClassCastException",
        "jl_ArrayIndexOutOfBoundsException",
        "sjsr_UndefinedBehaviorError",
        "js_CloneNotSupportedException"
    )

    val scalaClassDefs = linkingUnit.classDefs.filter(_.kind.isClass)

    val classesWithInstantiatedSubclasses = scalaClassDefs
      .withFilter(_.hasInstances)
      .flatMap(_.superClass)
      .map(_.name)
      .toSet

    def enableInlineableInitFor(classDef: LinkedClass): Boolean = {
      /* We can enable inlined init if all of the following apply:
       * - The class is not blacklisted
       * - It does not have any instantiated subclass
       * - It has exactly one constructor
       *
       * By construction, this is always true for module classes.
       */
      !blackList(classDef.encodedName) &&
      !classesWithInstantiatedSubclasses(classDef.encodedName) && {
        classDef.memberMethods.count(
            x => Definitions.isConstructorName(x.value.encodedName)) == 1
      }
    }

    scalaClassDefs
      .withFilter(enableInlineableInitFor(_))
      .map(_.encodedName)
      .toSet
  }

  abstract class KnowledgeAccessor extends GlobalKnowledge with Invalidatable {
    /* In theory, a KnowledgeAccessor should *contain* a GlobalKnowledge, not
     * *be* a GlobalKnowledge. We organize it that way to reduce memory
     * footprint and pointer indirections.
     */

    def isParentDataAccessed: Boolean =
      askIsParentDataAccessed(this)

    def isInterface(className: String): Boolean =
      classes(className).askIsInterface(this)

    def getAllScalaClassFieldDefs(className: String): List[FieldDef] =
      classes(className).askAllScalaClassFieldDefs(this)

    def hasInlineableInit(className: String): Boolean =
      classes(className).askHasInlineableInit(this)

    def hasStoredSuperClass(className: String): Boolean =
      classes(className).askHasStoredSuperClass(this)

    def getJSClassCaptureTypes(className: String): Option[List[Type]] =
      classes(className).askJSClassCaptureTypes(this)

    def getJSNativeLoadSpec(className: String): Option[JSNativeLoadSpec] =
      classes(className).askJSNativeLoadSpec(this)

    def getSuperClassOfJSClass(className: String): String =
      classes(className).askJSSuperClass(this)

    def getJSClassFieldDefs(className: String): List[FieldDef] =
      classes(className).askJSClassFieldDefs(this)
  }

  private class Class(initClass: LinkedClass,
      initHasInlineableInit: Boolean)
      extends Unregisterable {

    private var isAlive: Boolean = true

    private var isInterface = computeIsInterface(initClass)
    private var hasInlineableInit = initHasInlineableInit
    private var hasStoredSuperClass = computeHasStoredSuperClass(initClass)
    private var jsClassCaptureTypes = computeJSClassCaptureTypes(initClass)
    private var jsNativeLoadSpec = computeJSNativeLoadSpec(initClass)
    private var superClass = computeSuperClass(initClass)
    private var fieldDefs = computeFieldDefs(initClass)

    private val isInterfaceAskers = mutable.Set.empty[Invalidatable]
    private val hasInlineableInitAskers = mutable.Set.empty[Invalidatable]
    private val hasStoredSuperClassAskers = mutable.Set.empty[Invalidatable]
    private val jsClassCaptureTypesAskers = mutable.Set.empty[Invalidatable]
    private val jsNativeLoadSpecAskers = mutable.Set.empty[Invalidatable]
    private val superClassAskers = mutable.Set.empty[Invalidatable]
    private val fieldDefsAskers = mutable.Set.empty[Invalidatable]

    def update(linkedClass: LinkedClass, newHasInlineableInit: Boolean): Unit = {
      isAlive = true

      val newIsInterface = computeIsInterface(linkedClass)
      if (newIsInterface != isInterface) {
        isInterface = newIsInterface
        invalidateAskers(isInterfaceAskers)
      }

      if (newHasInlineableInit != hasInlineableInit) {
        hasInlineableInit = newHasInlineableInit
        invalidateAskers(hasInlineableInitAskers)
      }

      val newHasStoredSuperClass = computeHasStoredSuperClass(linkedClass)
      if (newHasStoredSuperClass != hasStoredSuperClass) {
        hasStoredSuperClass = newHasStoredSuperClass
        invalidateAskers(hasStoredSuperClassAskers)
      }

      val newJSClassCaptureTypes = computeJSClassCaptureTypes(linkedClass)
      if (newJSClassCaptureTypes != jsClassCaptureTypes) {
        jsClassCaptureTypes = newJSClassCaptureTypes
        invalidateAskers(jsClassCaptureTypesAskers)
      }

      val newJSNativeLoadSpec = computeJSNativeLoadSpec(linkedClass)
      if (newJSNativeLoadSpec != jsNativeLoadSpec) {
        jsNativeLoadSpec = newJSNativeLoadSpec
        invalidateAskers(jsNativeLoadSpecAskers)
      }

      val newSuperClass = computeSuperClass(linkedClass)
      if (newSuperClass != superClass) {
        superClass = newSuperClass
        invalidateAskers(superClassAskers)
      }

      val newFieldDefs = computeFieldDefs(linkedClass)
      if (newFieldDefs != fieldDefs) {
        fieldDefs = newFieldDefs
        invalidateAskers(fieldDefsAskers)
      }
    }

    private def computeIsInterface(linkedClass: LinkedClass): Boolean =
      linkedClass.kind == ClassKind.Interface

    private def computeHasStoredSuperClass(linkedClass: LinkedClass): Boolean =
      linkedClass.jsSuperClass.isDefined

    private def computeJSClassCaptureTypes(linkedClass: LinkedClass): Option[List[Type]] =
      linkedClass.jsClassCaptures.map(_.map(_.ptpe))

    private def computeJSNativeLoadSpec(linkedClass: LinkedClass): Option[JSNativeLoadSpec] =
      linkedClass.jsNativeLoadSpec

    private def computeSuperClass(linkedClass: LinkedClass): String =
      linkedClass.superClass.fold[String](null)(_.name)

    private def computeFieldDefs(linkedClass: LinkedClass): List[FieldDef] =
      linkedClass.fields

    private def invalidateAskers(askers: mutable.Set[Invalidatable]): Unit = {
      /* Calling `invalidateAndUnregisterFromAll()` will cause the
       * `Invalidatable` to call `unregister()` in this class, which will
       * mutate the `askers` set. Therefore, we cannot directly iterate over
       * `askers`, and need to take a snapshot instead.
       */
      val snapshot = askers.toSeq
      askers.clear()
      snapshot.foreach(_.invalidate())
    }

    def testAndResetIsAlive(): Boolean = {
      val result = isAlive
      isAlive = false
      result
    }

    def askIsInterface(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      isInterfaceAskers += invalidatable
      isInterface
    }

    def askAllScalaClassFieldDefs(invalidatable: Invalidatable): List[FieldDef] = {
      invalidatable.registeredTo(this)
      superClassAskers += invalidatable
      fieldDefsAskers += invalidatable
      val inheritedFieldDefs =
        if (superClass == null) Nil
        else classes(superClass).askAllScalaClassFieldDefs(invalidatable)
      inheritedFieldDefs ::: fieldDefs
    }

    def askHasInlineableInit(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      hasInlineableInitAskers += invalidatable
      hasInlineableInit
    }

    def askHasStoredSuperClass(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      hasStoredSuperClassAskers += invalidatable
      hasStoredSuperClass
    }

    def askJSClassCaptureTypes(invalidatable: Invalidatable): Option[List[Type]] = {
      invalidatable.registeredTo(this)
      jsClassCaptureTypesAskers += invalidatable
      jsClassCaptureTypes
    }

    def askJSNativeLoadSpec(invalidatable: Invalidatable): Option[JSNativeLoadSpec] = {
      invalidatable.registeredTo(this)
      jsNativeLoadSpecAskers += invalidatable
      jsNativeLoadSpec
    }

    def askJSSuperClass(invalidatable: Invalidatable): String = {
      invalidatable.registeredTo(this)
      superClassAskers += invalidatable
      superClass
    }

    def askJSClassFieldDefs(invalidatable: Invalidatable): List[FieldDef] = {
      invalidatable.registeredTo(this)
      fieldDefsAskers += invalidatable
      fieldDefs
    }

    def unregister(invalidatable: Invalidatable): Unit = {
      isInterfaceAskers -= invalidatable
      hasInlineableInitAskers -= invalidatable
      hasStoredSuperClassAskers -= invalidatable
      jsClassCaptureTypesAskers -= invalidatable
      jsNativeLoadSpecAskers -= invalidatable
      superClassAskers -= invalidatable
      fieldDefsAskers -= invalidatable
    }

    /** Call this when we invalidate all caches. */
    def unregisterAll(): Unit = {
      isInterfaceAskers.clear()
      hasInlineableInitAskers.clear()
      hasStoredSuperClassAskers.clear()
      jsClassCaptureTypesAskers.clear()
      jsNativeLoadSpecAskers.clear()
      superClassAskers.clear()
      fieldDefsAskers.clear()
    }
  }
}

private[emitter] object KnowledgeGuardian {
  private trait Unregisterable {
    def unregister(invalidatable: Invalidatable): Unit
  }

  trait Invalidatable {
    private val _registeredTo = mutable.Set.empty[Unregisterable]

    private[KnowledgeGuardian] def registeredTo(
        unregisterable: Unregisterable): Unit = {
      _registeredTo += unregisterable
    }

    /** To be overridden to perform subclass-specific invalidation.
     *
     *  All overrides should call the default implementation with `super` so
     *  that this `Invalidatable` is unregistered from the dependency graph.
     */
    def invalidate(): Unit = {
      _registeredTo.foreach(_.unregister(this))
      _registeredTo.clear()
    }
  }
}
