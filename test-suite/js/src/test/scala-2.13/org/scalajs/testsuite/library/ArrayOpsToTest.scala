/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package org.scalajs.testsuite.library

import scala.scalajs.js

import org.junit.Assert._
import org.junit.Test

class ArrayOpsToTest {

  @Test def to_T_issue_843(): Unit = {
    val array = js.Array(1,2,1,3,1,10,9)
    val list = array.to(List)
    assertArrayEquals(array.toArray, list.toArray)
  }

}
