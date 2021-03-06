package tests

import cdgp.solvers.OutputParserDreal3
import org.junit.Test
import org.junit.Assert._
import cdgp.{ConstParser, GetValueParser, ValueParseException}


final class TestParsers {

  // -------------------------------------------------------------
  // GetValueParser
  // -------------------------------------------------------------

  @Test
  def testGetValueParser_Pass(): Unit = {
    assertEquals( Map( "x" -> 1, "y" -> -2 ), GetValueParser("""((x 1)
               (y (- 2)))""").toMap)

    assertEquals( Map( "x" -> -7787, "y" -> 0 ), GetValueParser(""" ((x (- 7787))
               (y (- 0)))""").toMap)

    assertEquals( Map( "x" -> -7787, "y" -> -2 ), GetValueParser(""" ((x -7787)
               (y -2))""").toMap)

    assertEquals( Map( "x" -> "cdgp", "y" -> -2 ), GetValueParser(""" ((x "cdgp")
               (y -2))""").toMap)

    assertEquals( Map( "x" -> "cdgp", "y" -> -2, "z" -> "eps" ), GetValueParser(""" ((x "cdgp")
               (y -2)(z "eps"))""").toMap)
  }

  @Test
  def testGetValueParser_GetValueTooBigInt(): Unit = {
    try {
      GetValueParser("""((x 12345678901234)(y (- 2)))""").toMap
      fail()
    } catch { case e: Throwable => }
  }

  @Test
  def testGetValueParser_ParserString(): Unit = {
    val model = """((s "") (a 0) (b 0) (res1__2 "AAAAAAAAAA") (res2__2 "BAAAAAAAAA"))"""
    val parsed = GetValueParser(model).toMap
    assertEquals(Map("s" -> "", "a" -> 0, "b" -> 0, "res1__2" -> "AAAAAAAAAA", "res2__2" -> "BAAAAAAAAA"),
      parsed)
  }

  @Test
  def testGetValueParser_ParserReal(): Unit = {
    val model = """((a 0.0) (b 0.00123) (c -5.5) (d (- 3.3)) (e (- 2.2?)) (f 11.00811?))"""
    val parsed = GetValueParser(model).toMap
    assertEquals(Map("a" -> 0.0, "b" -> 0.00123, "c" -> -5.5, "d" -> -3.3, "e" -> -2.2, "f" -> 11.00811),
      parsed)
    assertEquals(Map("x" -> -0.125), GetValueParser("""((x (- (/ 1.0 8.0))))""").toMap)
  }

  @Test
  def testGetValueParser_Boolean(): Unit = {
    val model = """((a "true") (b true) (c false))"""
    val parsed = GetValueParser(model).toMap
    assertEquals(Map("a" -> "true", "b" -> true, "c" -> false),
      parsed)
  }

  @Test(expected=classOf[ValueParseException])
  def testGetValueParser_Fail(): Unit = {
    GetValueParser(""" ((x (- 7787))
      (y (- ERROR)))""")
  }

  @Test
  def testGetValueParser_Complex(): Unit = {
    val res = GetValueParser("""((a 15) (b 14) (c 3) (d 0) (res1__2a (- 16)) (res2__2a (- 32)))""")
    assertEquals(Map("a"->15, "b"->14, "c"->3, "d"->0, "res1__2a"->(-16), "res2__2a"->(-32)), res.toMap)
  }


  // -------------------------------------------------------------
  // ConstParser
  // -------------------------------------------------------------

  @Test
  def testConstParser_Pass(): Unit = {
    assertEquals(true, ConstParser("true"))
    assertEquals(false, ConstParser("false"))

    assertEquals("asd", ConstParser("\"asd\""))
    assertEquals("", ConstParser("\"\""))

    assertEquals(123, ConstParser("123"))
    assertEquals(-4, ConstParser("-4"))
    assertEquals(-4, ConstParser("(- 4)"))

    assertEquals(123.0, ConstParser("123.0"))
    assertEquals(1.25, ConstParser("1.25"))
    assertEquals(1.25, ConstParser("+1.25"))
    assertEquals(-4.5, ConstParser("-4.5"))
    assertEquals(1e-3, ConstParser("1e-3"))
    assertEquals(-1e-3, ConstParser("-1e-3"))
  }

  @Test(expected=classOf[ValueParseException])
  def testConstParser_Fail(): Unit = {
    ConstParser("[1, 2, 3]")
  }


  // -------------------------------------------------------------
  // Dreal3 Parser
  // -------------------------------------------------------------

  @Test
  def testParserDreal3_parse_unsat(): Unit = {
    val s = "unsat"
    val (dec, model) = OutputParserDreal3(s)
    assertEquals("unsat", dec)
    assertEquals(None, model)
  }

  @Test
  def testParserDreal3_parse_satPlain(): Unit = {
    val s = "delta-sat with delta = 0.00100000000000000"
    val (dec, model) = OutputParserDreal3(s)
    assertEquals("sat", dec)
    assertEquals(None, model)
  }

  @Test
  def testParserDreal3_parse_satModel1(): Unit = {
    val s = """Solution:
              |x : [ ENTIRE ] = [-2, -2]
              |delta-sat with delta = 0.00100000000000000""".stripMargin
    val (dec, model) = OutputParserDreal3(s)
    assertEquals("sat", dec)
    assertEquals(Some(Map("x"->(-2.0, -2.0))), model)
  }

  @Test
  def testParserDreal3_parse_satModel2(): Unit = {
    val s = """Solution:
              |x : [ ENTIRE ] = [-1.25, 1.25]
              |delta-sat with delta = 0.00100000000000000""".stripMargin
    val (dec, model) = OutputParserDreal3(s)
    assertEquals("sat", dec)
    assertEquals(Some(Map("x"->(-1.25, 1.25))), model)
  }

  @Test
  def testParserDreal3_parse_satModel3(): Unit = {
    val s = """Solution:
              |x : [ ENTIRE ] = [-INFTY, -INFTY]
              |y : [ ENTIRE ] = [+INFTY, +INFTY]
              |delta-sat with delta = 0.00100000000000000""".stripMargin
    val (dec, model) = OutputParserDreal3(s)
    assertEquals("sat", dec)
    assertEquals(Some(Map("x"->(Double.NegativeInfinity, Double.NegativeInfinity),
                          "y"->(Double.PositiveInfinity, Double.PositiveInfinity))), model)
  }
}