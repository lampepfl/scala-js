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

package java.lang

import scala.scalajs.js

@js.native
private trait ScalaJSClassData[A] extends js.Object {
  val name: String = js.native
  val isPrimitive: scala.Boolean = js.native
  val isInterface: scala.Boolean = js.native
  val isArrayClass: scala.Boolean = js.native
  val isRawJSType: scala.Boolean = js.native

  def isInstance(obj: Object): scala.Boolean = js.native
  def isAssignableFrom(that: ScalaJSClassData[_]): scala.Boolean = js.native

  def getSuperclass(): Class[_ >: A] = js.native
  def getComponentType(): Class[_] = js.native

  def newArrayOfThisClass(dimensions: js.Array[Int]): AnyRef = js.native
}

final class Class[A] private (data0: Object) extends Object {
  private val data: ScalaJSClassData[A] =
    data0.asInstanceOf[ScalaJSClassData[A]]

  override def toString(): String = {
    (if (isInterface()) "interface " else
        if (isPrimitive()) "" else "class ")+getName()
  }

  def isInstance(obj: Object): scala.Boolean =
    data.isInstance(obj)

  def isAssignableFrom(that: Class[_]): scala.Boolean =
    this.data.isAssignableFrom(that.data)

  def isInterface(): scala.Boolean =
    data.isInterface

  def isArray(): scala.Boolean =
    data.isArrayClass

  def isPrimitive(): scala.Boolean =
    data.isPrimitive

  private def isRawJSType(): scala.Boolean =
    data.isRawJSType

  def getName(): String =
    data.name

  def getSimpleName(): String =
    data.name.split('.').last.split('$').last

  def getSuperclass(): Class[_ >: A] =
    data.getSuperclass()

  def getComponentType(): Class[_] =
    data.getComponentType()

  @inline // optimize for the Unchecked case, where this becomes identity()
  def cast(obj: Object): A = {
    scala.scalajs.runtime.SemanticsUtils.asInstanceOfCheck(
        (this eq classOf[Nothing]) ||
        (obj != null && !isRawJSType && !isInstance(obj)),
        new ClassCastException("" + obj + " is not an instance of " + getName))
    obj.asInstanceOf[A]
  }

  // java.lang.reflect.Array support

  private[lang] def newArrayOfThisClass(dimensions: js.Array[Int]): AnyRef =
    data.newArrayOfThisClass(dimensions)
}
