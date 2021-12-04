package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.machine.{NGSM, NSST, ParikhSST}
import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso.math.Presburger.Sugar._

/** Unary transduction */
trait Transduction[C] {
  def usedAlphabet: Set[C]

  /**
    * Construct NSST that performs this transduction and has non-empty set of variables.
    *
    * @param alphabet
    * @return NSST that performs this transduction and has non-empty set of variables.
    */
  def toSST(alphabet: Set[C]): NSST[Int, C, C, Int]
}

object Transduction {

  case class Replace[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = (target.iterator ++ word.iterator).toSet

    override def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      val dfa = postfixDFA(target, alphabet)
      val edges = {
        // In each transition, DFA discards some prefix string (possibly empty one),
        // which is output by the transducer.
        for {
          q <- dfa.states
          a <- alphabet
        } yield {
          val (r, append) = dfa.transition.get((q, a)) match {
            case Some(r) if dfa.finalStates(r) => (r, word)
            case None /* q is final */         => (q, Seq(a))
            case Some(r) =>
              val qStored = target.take(q) :+ a
              (r, qStored.take(qStored.length - r))
          }
          (q, a, append, r)
        }
      }
      // On each state q, DFA has partially matched prefix of target string.
      val outGraph = dfa.states.map(q => q -> target.take(q % target.length))
      NGSM(dfa.states, alphabet, edges, dfa.q0, outGraph).toNSST.renamed
    }

  }

  case class ReplaceAll[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = target.toSet ++ word.toSet

    /** Construct NSST which replaces `target` input string with `word` */
    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      val dfa = postfixDFA(target, alphabet)
      val states = dfa.states -- dfa.finalStates
      val edges =
        for {
          q <- states
          a <- alphabet
        } yield {
          val r = dfa.transition((q, a))
          val append =
            if (dfa.finalStates(r)) word
            else {
              val qStored = target.take(q) :+ a
              qStored.take(qStored.length - r)
            }
          (q, a, append, r % target.length)
        }
      val outGraph = states.map(q => (q, target.take(q)))
      NGSM(states, alphabet, edges.toSet, dfa.q0, outGraph).toNSST.renamed
    }

  }

  /** x(i) := replace_some x(j) target word */
  case class ReplaceSome[C](target: Seq[C], word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = target.toSet ++ word.toSet

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      val dfa = postfixDFA(target, alphabet)
      val states = dfa.states -- dfa.finalStates
      val edges =
        for {
          q <- states
          a <- alphabet
          r <- dfa.transition.get(q, a).iterator
          append <- {
            val qStored = target.take(q) :+ a
            val opt = if (dfa.finalStates(r)) Some(word) else None
            Seq(qStored.take(qStored.length - (r % target.length))) ++ opt
          }
        } yield (q, a, append, r % target.length)
      val outGraph = states.map(q => (q, target.take(q)))
      NGSM(states, alphabet, edges, dfa.q0, outGraph).toNSST.renamed
    }
  }

  /** x(i) := insert(x(j), pos, word) */
  case class Insert[C](pos: Int, word: Seq[C]) extends Transduction[C] {

    override def usedAlphabet: Set[C] = word.toSet

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      type X = Int
      val x = 0
      type Q = Int
      type A = C
      type B = C
      type UpdateX = Update[X, B]
      type Edge = (Q, A, UpdateX, Q)
      val states = (0 to pos + 1).toSet
      val edges = states.flatMap { l =>
        if (l < pos) alphabet.map[Edge](a => (l, a, Map(x -> List(Cop1(x), Cop2(a))), l + 1))
        else if (l == pos)
          alphabet.map(a =>
            (l, a, Map(x -> (List(Cop1(x)) ++ word.map(c => Cop2(c)) ++ List(Cop2(a)))), l + 1)
          )
        else alphabet.map[Edge](a => (l, a, Map(x -> List(Cop1(x), Cop2(a))), l))
      }
      val outF = states
        .map(q =>
          q -> Set {
            if (q < pos) List(Cop1(x))
            else if (q == pos) List[Cop[X, B]](Cop1(x)) ++ word.map(c => Cop2(c))
            else List(Cop1(x))
          }
        )
        .toMap
      NSST(states, alphabet, Set(x), edges, 0, outF)
    }

  }

  /** x(i) := at(x(j), pos) */
  case class At[C](pos: Int) extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = Substr(pos, 1).toSST(alphabet)
  }

  /** x(i) := reverse(x(j)) */
  case class Reverse[C]() extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      NSST(
        Set(0),
        alphabet,
        Set(0),
        alphabet.map(a => (0, a, Map(0 -> List(Cop2(a), Cop1(0))), 0)),
        0,
        Map(0 -> Set(List(Cop1(0))))
      )
    }

  }

  /** x(i) := substr(x(j), from, len) */
  case class Substr[C](from: Int, len: Int) extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      val x = 0
      val states = (0 to from + len).toSet
      val edges = states.flatMap { q =>
        if (q < from) alphabet.map(a => (q, a, Map(x -> Nil), q + 1))
        else if (q < from + len) alphabet.map(a => (q, a, Map(x -> List(Cop1(x), Cop2(a))), q + 1))
        else alphabet.map(a => (q, a, Map(x -> List(Cop1(x))), q))
      }
      val outF = states.map(q => q -> Set(List[Cop[Int, C]](Cop1(x))))
      NSST(states, alphabet, Set(x), edges.toSet, 0, outF.toMap)
    }
  }

  /** x(i) is prefix of x(j) */
  case class TakePrefix[C]() extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      NSST(
        Set(0, 1),
        alphabet,
        Set(0),
        alphabet.flatMap(a =>
          Iterable(
            (0, a, Map(0 -> List(Cop1(0), Cop2(a))), 0),
            (0, a, Map(0 -> List(Cop1(0))), 1),
            (1, a, Map(0 -> List(Cop1(0))), 1)
          )
        ),
        0,
        Map(0 -> Set(List(Cop1(0))), 1 -> Set(List(Cop1(0))))
      )
    }

  }

  /** x(i) is suffix of x(j) */
  case class TakeSuffix[C]() extends Transduction[C] {

    override def usedAlphabet: Set[C] = Set.empty

    def toSST(alphabet: Set[C]): NSST[Int, C, C, Int] = {
      NSST(
        Set(0, 1),
        alphabet,
        Set(0),
        alphabet.flatMap(a =>
          Iterable(
            (0, a, Map(0 -> List(Cop1(0))), 0),
            (0, a, Map(0 -> List(Cop1(0), Cop2(a))), 1),
            (1, a, Map(0 -> List(Cop1(0), Cop2(a))), 1)
          )
        ),
        0,
        Map(0 -> Set(List(Cop1(0))), 1 -> Set(List(Cop1(0))))
      )
    }
  }

  /** 優先度を考慮する正規表現文字列置換。 名前は PCRE だが現在は JavaScript の意味論で動作する。
    */
  case class ReplacePCREAll[A, X](target: PCRE[A, X], replacement: Replacement[A, X])
      extends Transduction[A] {

    override def usedAlphabet: Set[A] = target.usedChars

    override def toSST(alphabet: Set[A]): NSST[Int, A, A, Int] = {
      val e = PCRE.Group(target.renameVars[Option[X]](Some.apply), None)
      val repl = replacement.word.map {
        case Left(a)  => Cop2(a)
        case Right(x) => Cop1(x)
      }
      CompileJavaScriptRegex.toReplaceAllSST(e, alphabet, repl.toList).renamed
      // CompilePerlRegex.replaceAllSST(target, replacement, alphabet)
    }

  }

  case class ReplacePCRE[A, X](target: PCRE[A, X], replacement: Replacement[A, X]) extends Transduction[A] {

    override def usedAlphabet: Set[A] = target.usedChars

    override def toSST(alphabet: Set[A]): NSST[Int, A, A, Int] = {
      val e = PCRE.Group(target.renameVars[Option[X]](Some.apply), None)
      val repl = replacement.word.map {
        case Left(a)  => Cop2(a)
        case Right(x) => Cop1(x)
      }
      CompileJavaScriptRegex.toReplaceFirstSST(e, alphabet, repl.toList).renamed
      //CompilePerlRegex.replaceSST(target, replacement, alphabet)
    }
  }

}

trait ParikhTransduction[C, I] {
  def usedAlphabet: Set[C]
  def toParikhSST(alphabet: Set[C]): ParikhSST[Int, C, C, Int, Int, I]
}

object ParikhTransduction {
  implicit class NSSTTransductionIsParikhTransduction[C, I](trans: Transduction[C])
      extends ParikhTransduction[C, I] {
    def usedAlphabet: Set[C] = trans.usedAlphabet

    def toParikhSST(alphabet: Set[C]): ParikhSST[Int, C, C, Int, Int, I] =
      trans.toSST(alphabet).toParikhSST

  }

  case class Substr[A, I](idxName: I, lenName: I) extends ParikhTransduction[A, I] {

    def usedAlphabet: Set[A] = Set.empty

    def toParikhSST(alphabet: Set[A]): ParikhSST[Int, A, A, Int, Int, I] = {
      import Presburger._
      val X = 0
      type T = Term[Either[I, Int]]
      val idx: T = Var(Left(idxName))
      val len: T = Var(Left(lenName))
      val input: T = Var(Right(0))
      val taken: T = Var(Right(1))
      val sought: T = Var(Right(2))
      val unit @ (unitX, unitL): (Update[Int, A], ParikhSST.ParikhUpdate[Int]) =
        (Map(X -> List(Cop1(X))), Map(0 -> 1, 1 -> 0, 2 -> 0))
      val edges = alphabet
        .flatMap { a =>
          val seek = (unitX, unitL + (2 -> 1))
          val take = (Map(X -> List(Cop1(X), Cop2(a))), unitL + (1 -> 1))
          val ignore = unit
          Iterable(
            (0, a, seek, 0),
            (0, a, take, 1),
            (1, a, take, 1),
            (1, a, ignore, 2),
            (2, a, ignore, 2)
          )
        }
        .map { case (q, a, (mx, mh), r) => (q, a, mx, mh, r) }
      val acceptFormulas = {
        val idxOutOrNegLen = idx < 0 || idx >= input || len <= 0
        Seq(
          idxOutOrNegLen ==> (taken === 0),
          (!idxOutOrNegLen && len <= input - idx) ==> (sought === idx && taken === len),
          (!idxOutOrNegLen && len > input - idx) ==> (sought === idx && taken === input - idx)
        )
      }
      ParikhSST[Int, A, A, Int, Int, I](
        Set(0, 1, 2),
        alphabet,
        Set(X),
        Set(0, 1, 2),
        Set(idxName, lenName),
        edges,
        0,
        (0 to 2).map((_, List(Cop1(X)), (0 to 2).map(_ -> 0).toMap)).toSet,
        acceptFormulas
      )
    }
  }
}

case class Replacement[A, X](word: Seq[Either[A, Option[X]]]) {
  def groupVars: Set[X] = word.collect { case Right(Some(x)) => x }.toSet
  lazy val indexed: Seq[Either[A, (Option[X], Int)]] = word
    .foldLeft((0, Seq.empty[Either[A, (Option[X], Int)]])) {
      case ((cur, acc), Left(a))  => (cur, Left(a) +: acc)
      case ((cur, acc), Right(x)) => (cur + 1, (Right(x, cur)) +: acc)
    }
    ._2
    .reverse
}
