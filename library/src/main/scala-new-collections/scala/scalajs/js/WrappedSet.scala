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

package scala.scalajs.js

import scala.collection.generic.CanBuildFrom
import scala.collection.mutable
import scala.collection.IterableFactory
import scala.scalajs.js

/** Wrapper to use a js.Set as a scala.mutable.Set */
@inline
class WrappedSet[T](val underlying: js.Set[T])
    extends mutable.AbstractSet[T]
       with mutable.SetOps[T, WrappedSet, WrappedSet[T]] {

  import WrappedSet._

  override def size(): Int =
    underlying.size

  override def contains(value: T): Boolean =
    underlying.has(value)

  override def clear(): Unit =
    underlying.clear()

  override def addOne(elem: T): this.type = {
    underlying.add(elem)
    this
  }

  override def subtractOne(elem: T): this.type = {
    underlying.remove(elem)
    this
  }

  override def add(elem: T): Boolean = {
    if (underlying.has(elem)) false
    else {
      underlying.add(elem)
      true
    }
  }

  override protected def fromSpecific(coll: IterableOnce[T]): WrappedSet[T] =
    WrappedSet.from(coll)

  override protected def newSpecificBuilder: mutable.Builder[T, WrappedSet[T]] =
    WrappedSet.newBuilder

  override def remove(elem: T): Boolean =
    underlying.delete(elem)

  override def iterableFactory: IterableFactory[WrappedSet] = WrappedSet

  override def iterator: scala.collection.Iterator[T] =
    new SetIterator(underlying)

  override def empty: WrappedSet[T] =
    new WrappedSet(js.Set.empty[T])
}

object WrappedSet extends IterableFactory[WrappedSet] {

  def empty[A]: WrappedSet[A] =
    new WrappedSet[A](js.Set.empty)

  def newBuilder[A]: mutable.Builder[A, WrappedSet[A]] = new WrappedSetBuilder[A]

  def from[A](source: IterableOnce[A]): WrappedSet[A] =
    (newBuilder[A] ++= source).result()

  private final class SetIterator[+T](dict: js.Set[T])
    extends scala.collection.Iterator[T] {

    private[this] val values = js.Array.from(dict.values())
    private[this] var index: Int = 0

    def hasNext(): Boolean = index < values.length

    def next(): T = {
      val value = values(index)
      index += 1
      value
    }
  }

  private final class WrappedSetBuilder[A]
    extends mutable.Builder[A, WrappedSet[A]] {

    private[this] var set: js.Set[A] = js.Set.empty

    @inline def addOne(elem: A): this.type = {
      set.add(elem)
      this
    }

    def clear(): Unit =
      set = js.Set.empty

    def result(): WrappedSet[A] =
      new js.WrappedSet(set)
  }



}

