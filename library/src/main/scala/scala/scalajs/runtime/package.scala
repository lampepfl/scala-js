package scala.scalajs

import scala.annotation.tailrec

import scala.collection.GenTraversableOnce

package object runtime {

  def wrapJavaScriptException(e: Any): Throwable = e match {
    case e: Throwable => e
    case _            => js.JavaScriptException(e)
  }

  def unwrapJavaScriptException(th: Throwable): Any = th match {
    case js.JavaScriptException(e) => e
    case _                         => th
  }

  def cloneObject(from: js.Object): js.Object = {
    val fromDyn = from.asInstanceOf[js.Dynamic]
    val result = js.Dynamic.newInstance(fromDyn.constructor)()
    val fromDict = from.asInstanceOf[js.Dictionary[js.Any]]
    val resultDict = result.asInstanceOf[js.Dictionary[js.Any]]
    for (key <- fromDict.keys)
      resultDict(key) = fromDict(key)
    result
  }

  @inline final def genTraversableOnce2jsArray[A](
      col: GenTraversableOnce[A]): js.Array[A] = {
    col match {
      case col: js.ArrayOps[A]     => col.result()
      case col: js.WrappedArray[A] => col.array
      case _ =>
        @noinline
        def unhappyPath() = {
          val result = new js.Array[A]
          col.foreach(x => result.push(x))
          result
        }
        unhappyPath()
    }
  }

  /** Dummy method used to preserve the type parameter of
   *  `js.constructorOf[T]` through erasure.
   *
   *  An early phase of the compiler reroutes calls to `js.constructorOf[T]`
   *  into `runtime.constructorOf(classOf[T])`.
   *
   *  The `clazz` parameter must be a literal `classOf[T]` constant such that
   *  `T` represents a class extending `js.Any` (not a trait nor an object).
   */
  def constructorOf(clazz: Class[_ <: js.Any]): js.Dynamic =
    throw new Error("stub")

  /** Public access to `new ConstructorTag` for the codegen of
   *  `js.ConstructorTag.materialize`.
   */
  def newConstructorTag[T <: js.Any](constructor: js.Dynamic): js.ConstructorTag[T] =
    new js.ConstructorTag[T](constructor)

  /** Returns an array of the enumerable properties in an object's prototype
   *  chain.
   *
   *  This is the implementation of [[js.Object.properties]].
   */
  def propertiesOf(obj: js.Any): js.Array[String] = {
    // See http://stackoverflow.com/questions/26445248/
    if (obj == null || js.isUndefined(obj)) {
      js.Array()
    } else {
      val result = new js.Array[String]
      val alreadySeen = js.Dictionary.empty[Boolean]

      @tailrec
      def loop(obj: js.Object): Unit = {
        if (obj != null) {
          // Add own enumerable properties that have not been seen yet
          val enumProps = js.Object.keys(obj)
          val enumPropsLen = enumProps.length
          var i = 0
          while (i < enumPropsLen) {
            val prop = enumProps(i)
            if (!alreadySeen.get(prop).isDefined)
              result.push(prop)
            i += 1
          }

          /* Add all own properties to the alreadySeen set, including
           * non-enumerable ones.
           */
          val allProps = js.Object.getOwnPropertyNames(obj)
          val allPropsLen = allProps.length
          var j = 0
          while (j < allPropsLen) {
            alreadySeen(allProps(j)) = true
            j += 1
          }

          // Continue with the next object in the prototype chain
          loop(js.Object.getPrototypeOf(obj))
        }
      }
      loop(js.Object(obj))

      result
    }
  }

  /** Information known at link-time, given the output configuration.
   *
   *  See [[LinkingInfo]] for details.
   */
  def linkingInfo: LinkingInfo = throw new Error("stub")

  /** Polyfill for fround in case we use strict Floats and even Typed Arrays
   *  are not available.
   *  Note: this method returns a Double, even though the value is meant
   *  to be a Float. It cannot return a Float because that would require to
   *  do `x.toFloat` somewhere in here, which would itself, in turn, call this
   *  method.
   */
  def froundPolyfill(v: Double): Double = {
    /* Originally inspired by the Typed Array polyfills written by Joshua Bell:
     * https://github.com/inexorabletash/polyfill/blob/a682f42c1092280bb01907c245979fb07219513d/typedarray.js#L150-L255
     * Then simplified quite a lot because
     * 1) we do not need to produce the actual bit string that serves as
     *    storage of the floats, and
     * 2) we are only interested in the float32 case.
     */
    import Math._

    // Special cases
    if (v.isNaN || v == 0.0 || v.isInfinite) {
      v
    } else {
      val LN2 = 0.6931471805599453
      val ebits = 8
      val fbits = 23
      val bias = (1 << (ebits-1)) - 1
      val twoPowFbits = (1 << fbits).toDouble
      val SubnormalThreshold = 1.1754943508222875E-38 // pow(2, 1-bias)

      val isNegative = v < 0
      val av = if (isNegative) -v else v

      val absResult = if (av >= SubnormalThreshold) {
        val e0 = floor(log(av) / LN2)
        // 1-bias <= e0 <= 1024
        if (e0 > bias) {
          // Overflow
          Double.PositiveInfinity
        } else {
          val twoPowE0 = pow(2, e0)
          val f0 = Bits.roundToEven(av / twoPowE0 * twoPowFbits)
          if (f0 / twoPowFbits >= 2) {
            //val e = e0 + 1.0 // not used
            val f = 1.0
            if (e0 > bias-1) { // === (e > bias) because e0 is whole
              // Overflow
              Double.PositiveInfinity
            } else {
              // Normalized case 1
              val twoPowE = 2*twoPowE0
              twoPowE * (1.0 + (f - twoPowFbits) / twoPowFbits)
            }
          } else {
            // Normalized case 2
            // val e = e0 // not used
            val f = f0
            val twoPowE = twoPowE0
            twoPowE * (1.0 + (f - twoPowFbits) / twoPowFbits)
          }
        }
      } else {
        // Subnormal
        val rounder = Float.MinPositiveValue.toDouble
        Bits.roundToEven(av / rounder) * rounder
      }

      if (isNegative) -absResult else absResult
    }
  }

}
