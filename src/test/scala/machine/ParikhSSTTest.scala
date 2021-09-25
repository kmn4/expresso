package com.github.kmn4.expresso.machine

import org.scalatest.funsuite.AnyFunSuite
import com.github.kmn4.expresso.language._
import com.github.kmn4.expresso.IntValuedOperation

class ParikhSSTTest extends AnyFunSuite {
  def testEquiv[A, B, I](t1: StringIntTransducer[A, B, I], t2: StringIntTransducer[A, B, I])(
      cases: Seq[(Seq[A], Map[I, Int])]
  ) = cases.foreach {
    case (w, i) =>
      val r1 = t1.transduce(w, i)
      val r2 = t2.transduce(w, i)
      if (r1 == r2) succeed
      else fail(s"$w:\n\tt1:\t${r1}\n\tt2\t${r2}")
  }

  def testExamples[A, B, I](t: StringIntTransducer[A, B, I])(cases: Seq[(Seq[A], Map[I, Int], Seq[B])]) =
    cases.foreach {
      case (w, i, o) =>
        val res = t.transduce(w, i)
        if (res.size != 1) fail(s"$w,$i:\toutput size is not one but ${res.size}")
        else if (res.head != o) fail(s"$w:\t\n\texpected:\t${o}\n\tgot:\t${res.head}")
        else succeed
    }

  def sizes[Q, A, B, X, L, I](p: ParikhSST[Q, A, B, X, L, I]) = {
    info(s"Q:\t${p.states.size}")
    info(s"X:\t${p.xs.size}")
    info(s"L:\t${p.ls.size}")
    info(s"Δ:\t${p.edges.size}")
    info(s"F:\t${p.outGraph.size}")
  }

  def substr(i: String, l: String) =
    ParikhTransduction.Substr(i, l).toParikhSST("abcd".toSet)
  val substr1 = substr("i", "l")
  test("substr transduction") {
    implicit def conv(t: (Int, Int)): Map[String, Int] = t match {
      case (i, l) => Map("i" -> i, "l" -> l)
    }
    testExamples(substr1)(
      Seq(
        ("abab", (0, 2), "ab"),
        ("abab", (2, 0), ""),
        ("abab", (1, 2), "ba"),
        ("bba", (1, 2), "ba"),
        ("aa", (-1, 2), ""),
        ("aa", (3, 2), ""),
        ("aa", (0, -2), "")
      )
    )
  }
  val substr2 = substr("j", "k")
  test("Compose two substr") {
    implicit def conv(t: (Int, Int, Int, Int)): Map[String, Int] = t match {
      case (i, l, j, k) => Map("i" -> i, "l" -> l, "j" -> j, "k" -> k)
    }
    val cases: Seq[(Seq[Char], Map[String, Int], Seq[Char])] = Seq(
      ("abab", (0, 3, 1, 2), "ba"),
      ("abab", (2, 3, 1, 2), "b"),
      ("abab", (-2, 3, 1, 2), ""),
      ("abab", (2, -3, 1, 2), ""),
      ("abab", (2, 3, 2, 0), ""),
      ("abab", (2, 3, -2, 0), ""),
      ("abab", (2, 3, 2, -1), ""),
      ("aabb", (1, 3, 0, 2), "ab"),
      ("aabb", (0, 4, 0, 4), "aabb"),
      ("abcd", (0, 4, 0, 4), "abcd")
    )
    val composed = substr1 compose substr2
    sizes(composed)
    testExamples(composed)(cases)
  }

  test("Compose three substr") {
    val substr3 = substr("s", "t")
    implicit def conv(t: (Int, Int, Int, Int, Int, Int)): Map[String, Int] = t match {
      case (i, l, j, k, s, t) => Map("i" -> i, "l" -> l, "j" -> j, "k" -> k, "s" -> s, "t" -> t)
    }
    val cases: Seq[(Seq[Char], Map[String, Int], Seq[Char])] = Seq(
      ("abcd", (0, 3, 1, 2, 1, 1), "c"),
      ("abcd", (0, 4, 0, 4, 0, 4), "abcd")
    )
    val composed = substr1 compose substr2 compose substr3
    sizes(composed)
    testExamples(composed)(cases)
  }

  test("Compose replaceAll and substr") {
    val replaceAll = Transduction.ReplaceAll("aab", "abc").toSST("abcd".toSet).toParikhSST[String, String]
    val composed = replaceAll compose substr1
    implicit def conv(n: (Int, Int)): Map[String, Int] = n match {
      case (i, l) => Map("i" -> i, "l" -> l)
    }
    val cases: Seq[(Seq[Char], Map[String, Int], Seq[Char])] = Seq(
      ("aabc", (0, 4), "abcc"),
      ("aabc", (0, 3), "abc"),
      ("aabc", (3, 10), "c"),
      ("aabc", (-1, 5), "")
    )
    testExamples(composed)(cases)
  }

  def indexOf0(word: String, i: String) =
    IntValuedOperation.IndexOf.IndexOfConst(word, 0, i).toParikhAutomaton("abcd".toSet).toIdentityParikhSST

  test("Compose replaceAll and indexOf") {
    val replaceAll = Transduction.ReplaceAll("aab", "abc").toSST("abcd".toSet).toParikhSST[String, String]
    val indexOfAB = indexOf0("ab", "i")
    testExamples(indexOfAB)(
      Seq(
        ("aab", Map("i" -> 1), "aab")
      )
    )
    val composed = replaceAll compose indexOfAB
    sizes(composed)
    Seq(
      ("aab", 0, Some("abc")),
      ("aab", 1, None),
      ("aab", 2, None),
      ("aab", -1, None),
      ("aaaab", 2, Some("aaabc"))
    ).foreach {
      case (in, i, out) =>
        val got = composed.transduce(in, Map("i" -> i))
        assert(got.size <= 1)
        assert(got.headOption == out.map(_.toSeq))
    }
  }
}
