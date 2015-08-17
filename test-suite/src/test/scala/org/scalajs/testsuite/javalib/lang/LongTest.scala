/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js Test Suite        **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2013, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */
package org.scalajs.testsuite.javalib.lang

import java.lang.{Long => JLong}

import org.scalajs.jasminetest.JasmineTest

/**
 * tests the implementation of the java standard library Long
 * requires jsinterop/LongTest to work to make sense
 */
object LongTest extends JasmineTest {

  describe("java.lang.Long") {
    it("should provide `reverseBytes`") {
      expect(JLong.reverseBytes(0xf5ab689cd401ff14L) == 0x14ff01d49c68abf5L).toBeTruthy
    }

    it("should provide `rotateLeft`") {
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 0) == 0xf5ab689cd401ff14L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 1) == 0xeb56d139a803fe29L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 8) == 0xab689cd401ff14f5L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 13) == 0x6d139a803fe29eb5L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 64) == 0xf5ab689cd401ff14L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 65) == 0xeb56d139a803fe29L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, 80) == 0x689cd401ff14f5abL).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, -1) == 0x7ad5b44e6a00ff8aL).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, -56) == 0xab689cd401ff14f5L).toBeTruthy
      expect(JLong.rotateLeft(0xf5ab689cd401ff14L, -70) == 0x53d6ada2735007fcL).toBeTruthy
    }

    it("should provide `rotateRight`") {
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 0) == 0xf5ab689cd401ff14L).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 1) == 0x7ad5b44e6a00ff8aL).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 8) == 0x14f5ab689cd401ffL).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 13) == 0xf8a7ad5b44e6a00fL).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 64) == 0xf5ab689cd401ff14L).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 65) == 0x7ad5b44e6a00ff8aL).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, 80) == 0xff14f5ab689cd401L).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, -1) == 0xeb56d139a803fe29L).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, -56) == 0x14f5ab689cd401ffL).toBeTruthy
      expect(JLong.rotateRight(0xf5ab689cd401ff14L, -70) == 0x6ada2735007fc53dL).toBeTruthy
    }

    it("should implement bitCount") {
      expect(JLong.bitCount(0L)).toEqual(0)
      expect(JLong.bitCount(35763829229342837L)).toEqual(26)
      expect(JLong.bitCount(-350003829229342837L)).toEqual(32)
    }

    it("should provide `compareTo`") {
      def compare(x: Long, y: Long): Int =
        new JLong(x).compareTo(new JLong(y))

      expect(compare(0L, 5L)).toBeLessThan(0)
      expect(compare(10L, 9L)).toBeGreaterThan(0)
      expect(compare(-2L, -1L)).toBeLessThan(0)
      expect(compare(3L, 3L)).toEqual(0)
    }

    it("should be a Comparable") {
      def compare(x: Any, y: Any): Int =
        x.asInstanceOf[Comparable[Any]].compareTo(y)

      expect(compare(0L, 5L)).toBeLessThan(0)
      expect(compare(10L, 9L)).toBeGreaterThan(0)
      expect(compare(-2L, -1L)).toBeLessThan(0)
      expect(compare(3L, 3L)).toEqual(0)
    }

    it("should parse strings") {
      def test(s: String, v: Long): Unit = {
        expect(JLong.parseLong(s)).toEqual(v)
        expect(JLong.valueOf(s).longValue()).toEqual(v)
        expect(new JLong(s).longValue()).toEqual(v)
      }

      test("0", 0L)
      test("5", 5L)
      test("127", 127L)
      test("-100", -100L)
      test("30000", 30000L)
      test("-90000", -90000L)
      test("4", 4L)
      test("-4", -4L)
      test("4000000000", 4000000000L)
      test("-18014398509482040", -18014398509482040L)
    }

    it("should reject invalid strings when parsing") {
      def test(s: String): Unit =
        expect(() => JLong.parseLong(s)).toThrow

      test("abc")
      test("asdf")
      test("")
    }

    it("should parse strings in base 16") {
      def test(s: String, v: Long): Unit = {
        expect(JLong.parseLong(s, 16)).toEqual(v)
        expect(JLong.valueOf(s, 16).longValue()).toEqual(v)
      }

      test("0", 0x0L)
      test("5", 0x5L)
      test("ff", 0xffL)
      test("-24", -0x24L)
      test("30000", 0x30000L)
      test("-90000", -0x90000L)
      test("bfc94973", 3217639795L)
      test("bfc949733", 51482236723L)
    }

    it("should parse strings in bases 2 to 36") {
      def test(radix: Int, s: String, v: Long): Unit = {
        expect(JLong.parseLong(s, radix)).toEqual(v)
        expect(JLong.valueOf(s, radix).longValue()).toEqual(v)
      }

      def genTestValue(i: Int): Long = {
        val result = Long.MaxValue / (1L << i)
        if (i > 63) -result
        else result
      }

      for {
        radix <- 2 to 36
        i <- 0 until 128
      } {
        val n = genTestValue(i)
        test(radix, JLong.toString(n, radix), n)
      }
    }

    it("should reject parsing strings when base < 2 || base > 36") {
      def test(s: String, radix: Int): Unit = {
        expect(() => JLong.parseLong(s, radix)).toThrow()
        expect(() => JLong.valueOf(s, radix).longValue()).toThrow()
      }

      List[Int](-10, -5, 0, 1, 37, 38, 50, 100).foreach(test("5", _))
    }

    it("should implement toString without radix") {
      expect(Int.MaxValue.toLong.toString).toEqual("2147483647")
      expect((-50L).toString).toEqual("-50")
      expect((-1000000000L).toString).toEqual("-1000000000")
      expect((Int.MaxValue.toLong+1L).toString).toEqual("2147483648")
      expect(Int.MinValue.toLong.toString).toEqual("-2147483648")

      /* Ported from
       * https://github.com/gwtproject/gwt/blob/master/user/test/com/google/gwt/emultest/java/lang/JLongTest.java
       */
      expect(new JLong(89000000005L).toString).toEqual("89000000005")
      expect(new JLong(JLong.MIN_VALUE).toString).toEqual("-9223372036854775808")
      expect(new JLong(JLong.MAX_VALUE).toString).toEqual("9223372036854775807")
      expect(JLong.toString(-80765L)).toEqual("-80765")
      expect(JLong.toString(80765L)).toEqual("80765")
      expect(JLong.toString(Integer.MIN_VALUE.toLong)).toEqual("-2147483648")
      expect(JLong.toString(Integer.MAX_VALUE.toLong)).toEqual("2147483647")
      expect(JLong.toString(-89000000005L)).toEqual("-89000000005")
      expect(JLong.toString(89000000005L)).toEqual("89000000005")
      expect(JLong.toString(JLong.MIN_VALUE)).toEqual("-9223372036854775808")
      expect(JLong.toString(JLong.MAX_VALUE)).toEqual("9223372036854775807")
    }

    it("should implement toString with radix") {
      /* Ported from
       * https://github.com/gwtproject/gwt/blob/master/user/test/com/google/gwt/emultest/java/lang/JLongTest.java
       */
      expect(JLong.toString(100000000L, 10)).toEqual("100000000")
      expect(JLong.toString(8589934591L, 8)).toEqual("77777777777")
      expect(JLong.toString(68719476735L, 16)).toEqual("fffffffff")
      expect(JLong.toString(8796093022207L, 2)).toEqual("1111111111111111111111111111111111111111111")
      expect(JLong.toString(0x8000000000000000L, 10)).toEqual("-9223372036854775808")
      expect(JLong.toString(0x7fffffffffffffffL, 10)).toEqual("9223372036854775807")
      expect(JLong.toString(0x8000000000000000L, 16)).toEqual("-8000000000000000")
      expect(JLong.toString(0x7fffffffffffffffL, 16)).toEqual("7fffffffffffffff")
    }

    it("should provide `highestOneBit`") {
      expect(JLong.highestOneBit(0L) == 0L).toBeTruthy
      expect(JLong.highestOneBit(-1L) == Long.MinValue).toBeTruthy
      expect(JLong.highestOneBit(-256L) == Long.MinValue).toBeTruthy
      expect(JLong.highestOneBit(1L) == 1L).toBeTruthy
      expect(JLong.highestOneBit(0x88L) == 0x80L).toBeTruthy
      expect(JLong.highestOneBit(Long.MaxValue) == 0x4000000000000000L).toBeTruthy
      expect(JLong.highestOneBit(Long.MinValue) == Long.MinValue).toBeTruthy
      expect(JLong.highestOneBit(0x32100012300L) == 0x20000000000L).toBeTruthy
    }

    it("should provide `lowestOneBit`") {
      expect(JLong.lowestOneBit(0L) == 0L).toBeTruthy
      expect(JLong.lowestOneBit(-1L) == 1L).toBeTruthy
      expect(JLong.lowestOneBit(-256L) == 256L).toBeTruthy
      expect(JLong.lowestOneBit(12L) == 4L).toBeTruthy
      expect(JLong.lowestOneBit(0x88L) == 0x8L).toBeTruthy
      expect(JLong.lowestOneBit(Long.MaxValue) == 1L).toBeTruthy
      expect(JLong.lowestOneBit(Long.MinValue) == Long.MinValue).toBeTruthy
      expect(JLong.lowestOneBit(0x32100012300L) == 0x100L).toBeTruthy
    }

    it("should implement toBinaryString") {
      // scalastyle:off disallow.space.before.token disallow.space.after.token line.size.limit
      expect(JLong.toBinaryString(              0L)).toEqual("0")
      expect(JLong.toBinaryString(             -1L)).toEqual("1111111111111111111111111111111111111111111111111111111111111111")
      expect(JLong.toBinaryString(      456324454L)).toEqual("11011001100101111010101100110")
      expect(JLong.toBinaryString(     -456324454L)).toEqual("1111111111111111111111111111111111100100110011010000101010011010")
      expect(JLong.toBinaryString( 98765432158845L)).toEqual("10110011101001110011110011111111111101001111101")
      expect(JLong.toBinaryString(-49575304457780L)).toEqual("1111111111111111110100101110100101011001100101101001000111001100")
      expect(JLong.toBinaryString(Long.MinValue   )).toEqual("1000000000000000000000000000000000000000000000000000000000000000")
      expect(JLong.toBinaryString(Long.MaxValue   )).toEqual("111111111111111111111111111111111111111111111111111111111111111")
      // scalastyle:on disallow.space.before.token disallow.space.after.token line.size.limit
    }

    it("should implement toHexString") {
      // scalastyle:off disallow.space.before.token disallow.space.after.token
      expect(JLong.toHexString(              0L)).toEqual("0")
      expect(JLong.toHexString(             -1L)).toEqual("ffffffffffffffff")
      expect(JLong.toHexString(      456324454L)).toEqual("1b32f566")
      expect(JLong.toHexString(     -456324454L)).toEqual("ffffffffe4cd0a9a")
      expect(JLong.toHexString( 98765432158845L)).toEqual("59d39e7ffa7d")
      expect(JLong.toHexString(-49575304457780L)).toEqual("ffffd2e9599691cc")
      expect(JLong.toHexString(Long.MinValue   )).toEqual("8000000000000000")
      expect(JLong.toHexString(Long.MaxValue   )).toEqual("7fffffffffffffff")
      // scalastyle:on disallow.space.before.token disallow.space.after.token
    }

    it("should implement toOctalString") {
      // scalastyle:off disallow.space.before.token disallow.space.after.token
      expect(JLong.toOctalString(              0L)).toEqual("0")
      expect(JLong.toOctalString(             -1L)).toEqual("1777777777777777777777")
      expect(JLong.toOctalString(      456324454L)).toEqual("3314572546")
      expect(JLong.toOctalString(     -456324454L)).toEqual("1777777777774463205232")
      expect(JLong.toOctalString( 98765432158845L)).toEqual("2635163637775175")
      expect(JLong.toOctalString(-49575304457780L)).toEqual("1777776456453145510714")
      expect(JLong.toOctalString(Long.MinValue   )).toEqual("1000000000000000000000")
      expect(JLong.toOctalString(Long.MaxValue   )).toEqual("777777777777777777777")
      // scalastyle:on disallow.space.before.token disallow.space.after.token
    }

    it("should correctly compute trailing zeros") {
      expect(JLong.numberOfTrailingZeros(0xff10000000000000L)).toEqual(52)
      expect(JLong.numberOfTrailingZeros(0xff20000000000000L)).toEqual(53)
      expect(JLong.numberOfTrailingZeros(0xff40000000000000L)).toEqual(54)
      expect(JLong.numberOfTrailingZeros(0xff80000000000000L)).toEqual(55)

      expect(JLong.numberOfTrailingZeros(0x0000010000000000L)).toEqual(40)
      expect(JLong.numberOfTrailingZeros(0x0000020000000000L)).toEqual(41)
      expect(JLong.numberOfTrailingZeros(0x0000040000000000L)).toEqual(42)
      expect(JLong.numberOfTrailingZeros(0x0000080000000000L)).toEqual(43)

      expect(JLong.numberOfTrailingZeros(0x0000000000010000L)).toEqual(16)
      expect(JLong.numberOfTrailingZeros(0x0000000000020000L)).toEqual(17)
      expect(JLong.numberOfTrailingZeros(0x0000000000040000L)).toEqual(18)
      expect(JLong.numberOfTrailingZeros(0x0000000000080000L)).toEqual(19)
    }

    it("should implement signum") {
      //check a few ints
      expect(JLong.signum(-11)).toEqual(-1)
      expect(JLong.signum(-1)).toEqual(-1)
      expect(JLong.signum(0)).toEqual(0)
      expect(JLong.signum(1)).toEqual(1)
      expect(JLong.signum(11)).toEqual(1)

      //check a few longs
      expect(JLong.signum(Long.MinValue)).toEqual(-1)
      expect(JLong.signum(-98765432158845L)).toEqual(-1)
      expect(JLong.signum(-49575304457780L)).toEqual(-1)
      expect(JLong.signum(-11L)).toEqual(-1)
      expect(JLong.signum(-1L)).toEqual(-1)
      expect(JLong.signum(0L)).toEqual(0)
      expect(JLong.signum(1L)).toEqual(1)
      expect(JLong.signum(11L)).toEqual(1)
      expect(JLong.signum(49575304457780L)).toEqual(1)
      expect(JLong.signum(98765432158845L)).toEqual(1)
      expect(JLong.signum(Long.MaxValue)).toEqual(1)
    }
  }
}
