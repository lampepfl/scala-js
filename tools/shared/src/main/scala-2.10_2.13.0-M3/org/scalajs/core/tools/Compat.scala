package org.scalajs.core.tools

import scala.collection.Traversable
import scala.collection.mutable

// Makes 2.13 API available to older versions of the Scala library
private[tools] object Compat {

  /**
    * Adds a `filterInPlace` operation to mutable Maps. In 2.13, `retain` has been
    * deprecated in favor of `filterInPlace`.
    */
  implicit class MutableMapHasFilterInPlace[K, V](map: mutable.Map[K, V]) {
    def filterInPlace(p: ((K, V)) => Boolean): mutable.Map[K, V] = map.retain((k, v) => p((k, v)))
  }

  type NonDeprecatedTraversable[+A] = Traversable[A]
  type NonDeprecatedImmutableTraversable[+A] = scala.collection.immutable.Traversable[A]

}
