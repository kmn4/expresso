package com.github.kmn4.expresso.language

import org.scalatest.funsuite._
import com.github.kmn4.expresso.language.PCRE._
import org.scalactic.source.Position

class ReplacerTest extends AnyFunSuite {
  import CompilePerlRegex.{ParsedChar, Parsed}

  def empty: PCRE[Char, String] = Empty()
  def eps: PCRE[Char, String] = Eps()
  implicit def chars(s: String): PCRE[Char, String] = Chars(s.toSet)
  def cat(es: PCRE[Char, String]*): PCRE[Char, String] = es.fold(eps)(Cat.apply[Char, String])
  def alt(e1: PCRE[Char, String], e2: PCRE[Char, String]): PCRE[Char, String] = Alt(e1, e2)
  def greedy(e: PCRE[Char, String]): PCRE[Char, String] = Greedy(e)
  def nonGreedy(e: PCRE[Char, String]): PCRE[Char, String] = NonGreedy(e)
  def group(e: PCRE[Char, String], x: String): PCRE[Char, String] = Group(e, x)
  def dot: PCRE[Char, String]                                                 = PCRE.AllChar()

  def firstMatch[A, X](e: PCRE[A, X]): PCRE[A, X] =
    PCRE.Cat(PCRE.Cat(PCRE.NonGreedy(PCRE.Chars(e.usedChars)), e), PCRE.Greedy(PCRE.Chars(e.usedChars)))

  def repetitiveMatch[A, X](e: PCRE[A, X]): PCRE[A, X] = PCRE.Greedy(PCRE.Alt(e, PCRE.Chars(e.usedChars)))

  def prettyParsedChar(c: ParsedChar[Char, String]): String = c match {
    case Left(a)        => a.toString()
    case Right(LPar(x)) => s"(<$x>"
    case Right(RPar(x)) => s")<$x>"
  }
  def prettyParsed(w: Parsed[Char, String]): String = w.map(prettyParsedChar).mkString

  // Set of alphabet used in all of tests in this class.
  val alphabet = ('a' to 'z').toSet

  def exec(e: PCRE[Char, String], w: Seq[Char]) = {
    val p         = CompilePerlRegex.toParser(e, alphabet)
    val parsedSet = p.transduce(w).map(prettyParsed)
    assert(parsedSet.size <= 1)
    val parseResult = parsedSet.headOption.map(w => s"""\"$w\"""").getOrElse("No match")
    info(s"""\"$w\" => $parseResult""")
  }

  def execAll(e: PCRE[Char, String])(cases: Seq[Char]*) = test(s"$e") {
    cases.foreach(w => exec(e, w))
  }

  execAll(greedy(alt(group(cat("a", greedy(alt("b", "c"))), "x"), "abc")))("babcaaccca", "")
  execAll(greedy(group(alt("a", eps), "x")))("aaa", "")
  execAll(group(cat(greedy("a"), group(greedy("b"), "y")), "x"))("aaabba", "", "bb")
  execAll(firstMatch(group(cat(greedy("a"), group(greedy("b"), "y")), "x")))("aaabba", "", "bb")
  execAll(repetitiveMatch(group(cat(greedy("a"), group(greedy("b"), "y")), "x")))("aaabba", "", "bb")

  def replacementToString(r: Replacement[Char, String]) = r.word.map {
    case Left(c)        => c.toString()
    case Right(Some(x)) => s"$$<$x>"
    case Right(None)    => s"$$&"
  }.mkString

  def testReplaceAll(e: PCRE[Char, String], replacement: Replacement[Char, String])(
      cases: (Seq[Char], Seq[Char])*
  )(implicit pos: Position) = test(s"ReplaceAll:\t$e\t=> ${replacementToString(replacement)}") {
    val s = Transduction.ReplacePCREAll(e, replacement).toSST(alphabet)
    for ((w, expected) <- cases) {
      val got = s.transduce(w)
      assert(got.size == 1)
      assert(got.head == expected)
    }
  }

  def testReplace(e: PCRE[Char, String], replacement: Replacement[Char, String])(
      cases: (Seq[Char], Seq[Char])*
  )(implicit pos: Position) = test(s"ReplaceAll:\t$e\t=>\t${replacementToString(replacement)}") {
    val s = Transduction.ReplacePCRE(e, replacement).toSST(alphabet)
    for ((w, expected) <- cases) {
      val got = s.transduce(w)
      assert(got.size == 1)
      assert(got.head == expected)
    }
  }

  def replacement(w: Any*): Replacement[Char, String] = Replacement(
    w.collect {
      case c: Char   => Left(c)
      case s: String => Right(Some(s))
      case 0         => Right(None)
    }
  )

  // a => b
  testReplace("a", replacement('b'))(
    ("", ""),
    ("aaa", "baa"),
    ("baa", "bba"),
    ("bbb", "bbb")
  )

  // a(b|c)* => a$&a
  testReplaceAll(cat("a", greedy(alt("b", "c"))), replacement('a', 0, 'a'))(
    ("abc", "aabca"),
    ("abca", "aabcaaaa")
  )

  // (?<x>a*)(?<y>b*)(?<z>c*) => $<z>$<y>$<x>
  testReplaceAll(
    cat(group(greedy("a"), "x"), group(greedy("b"), "y"), group(greedy("c"), "z")),
    replacement("z", "y", "x")
  )(("aabbcc", "ccbbaa"), ("bbc", "cbb"), ("bab", "bba"))

  // ([ab])* => $&$&$&
  testReplaceAll(greedy("ab"), replacement(0, 0, 0))(("ab", "ababab"), ("", ""), ("b", "bbb"))

  // (?<z>(?<x>a*)(?<y>b*))	=> $<x>$<y>$<z>
  testReplaceAll(
    group(cat(group(greedy("a"), "x"), group(greedy("b"), "y")), "z"),
    replacement("x", "y", "z")
  )(
    ("ab", "abab"),
    ("ba", "bbaa"),
    ("", "")
  )

  // a* => ($&)
  testReplaceAll(greedy("a"), replacement('(', 0, ')'))(("", "()"), ("a", "(a)()"))
  // a*?b => c
  testReplaceAll(cat(nonGreedy("a"), "b"), replacement('c'))(("baab", "cc"))
  // a*b => c
  testReplaceAll(cat(greedy("a"), "b"), replacement('c'))(("baab", "cc"))
  // [abc]*?b => c
  testReplaceAll(cat(nonGreedy("abc"), "b"), replacement('c'))(("abb", "cc"))
  // [abc]*b => c
  testReplaceAll(cat(greedy("abc"), "b"), replacement('c'))(("abb", "c"))
  // (?<x>[abc]*?)b => c$<x>
  testReplaceAll(cat(group(nonGreedy("abc"), "x"), "b"), replacement('c', "x"))(("abb", "cac"))

  // (?<x>.) => ($<x>)
  testReplaceAll(group(dot, "x"), replacement('(', "x", ')'))(("aba", "(a)(b)(a)"))
  // (?<x>(?<y>.*?)*) => [$<y>,$<x>]
  testReplaceAll(group(greedy(group(dot, "y")), "x"), replacement('[', "y", ',', "x", ']'))(
    ("abc", "[c,abc][,]")
  )
  // (?<x>|.) => ($<x>)
  testReplaceAll(group(alt(eps, dot), "x"), replacement('(', "x", ')'))(
    ("aba", "()a()b()a()") // これは JS の場合。PCRE では "()(a)()(b)()(a)()" が正しい
  )
  // (?<x>aa*) => ($<x>)
  testReplaceAll(group(cat("a", greedy("a")), "x"), replacement('(', "x", ')'))(
    ("a", "(a)"),
    ("bbaabab", "bb(aa)b(a)b"),
    ("aabbabb", "(aa)bb(a)bb")
  )
  // ((?<x>a)*b)* => [($&),($<x>)]
  testReplaceAll(greedy(cat(greedy(group("a", "x")), "b")), replacement('[', 0, ',', "x", ']'))(
    ("abb", "[abb,][,]")
  )

  // Bugs (nullable regexes that put higher precedence on the empty string)
  // testReplaceAll(eps, replacement('(', 0, ')'))(("a", "()a()"))
  // testReplaceAll(alt(eps, "a"), replacement('(', 0, ')'))(("", "()"), ("a", "()(a)()"))
  // testReplaceAll(nonGreedy("a"), replacement('(', 0, ')'))(("", "()"), ("a", "()(a)()"))
  // testReplaceAll(
  //   cat(group(greedy("a"), "x"), group(nonGreedy("b"), "y")),
  //   replacement('(', "y", "x", ')')
  // )(("ab", "(a)()(b)()"))
}
