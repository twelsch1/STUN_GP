package tests

import cdgp._
import org.junit.Test
import org.junit.Assert._

class TestTools {
  @Test
  def test_allOccurences(): Unit = {
    assertEquals(List(0, 8), Tools.allOccurences("asd fgh asd", "a"))
    assertEquals(List(), Tools.allOccurences("asd fgh asd", "z"))
    assertEquals(List(0, 1, 2), Tools.allOccurences("aaa", "a"))
  }

  @Test
  def test_convertHexToChars(): Unit = {
    assertEquals("asd fgh", Tools.convertToJavaString("asd fgh"))
    assertEquals(" A ", Tools.convertToJavaString(" \\x41 "))
    assertEquals("\n", Tools.convertToJavaString("\\n"))
    assertEquals("as\nas", Tools.convertToJavaString("as\\nas"))
    assertEquals("\"", Tools.convertToJavaString("\"\""))
  }
}
