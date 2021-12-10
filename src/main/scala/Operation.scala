package com.github.kmn4.expresso

import com.github.kmn4.expresso.language.Constraint
import com.github.kmn4.expresso.language.ParikhLanguage
import com.github.kmn4.expresso.language.postfixDFA
import com.github.kmn4.expresso.machine.ParikhAutomaton
import com.github.kmn4.expresso.math.Presburger
import com.github.kmn4.expresso.math.Presburger.Sugar._
import com.github.kmn4.expresso.smttool.SimpleQualID
import com.github.kmn4.expresso.smttool.Strings
import smtlib.theories.Ints
import smtlib.trees.Terms
import smtlib.trees.Terms.SNumeral

// Parikh オートマトンや Parikh SST で表して扱う文字列操作．
sealed trait Operation {
  // 値域のソート．IntSort と StringSort のいずれかである．
  def rangeSort: Terms.Sort
  // SMT-LIB の項 t がこの操作を適用する項であり，機械へ変換可能な表現を抽出できる．
  def extractable(t: Terms.Term): Boolean
}

object Operation {
  val builtins: Seq[Operation] = IntValuedOperation.builtins ++ StringValuedOperation.builtins
}

trait IntValuedOperation extends Operation {
  /**
    * この操作 f が i = f(x, i1, ..., in) のように使われているとき，
    * x \in Lang(i, i1, ..., in) がこの等式と等価になるような言語．
    */
  type Lang <: ParikhLanguage[Char, String]

  override def rangeSort: Terms.Sort = Ints.IntSort()
  override def extractable(t: Terms.Term): Boolean = extractThis.isDefinedAt(t)

  // extractThis と同様だが，値の型を (i, x \in L) に変形する．
  final def expectInt: PartialFunction[Terms.Term, (String, Constraint.ParikhAssertion[String])] =
    extractThis andThen { case (i, x, l) => (i, Constraint.ParikhAssertion(x, l)) }

  /**
    * SMT-LIB の項 t がこの操作を適用する項であるなら，機械へ変換可能な表現を抽出する．
    * 結果の組 (i, x, L) の意味：条件 x \in L の下で t の値が i に等しい．
    *
    * 実装では { case SimpleApp("str.indexof", SString(w), t) => ... } のように書く．
    * t が整数式なら，... 部分では t が変数と定数のいずれかであることを仮定してよい．
    */
  def extractThis: PartialFunction[Terms.Term, (String, String, Lang)]
}

object IntValuedOperation {
  val builtins: Seq[IntValuedOperation] = Seq(
    Length,
    CountChar,
    IndexOf,
    CodeAt
  )

  def abstractA(a: Terms.Term): (String, Seq[Presburger.Formula[Either[String, Int]]]) = a match {
    case SimpleQualID(i) => (i, Seq.empty)
    case Terms.SNumeral(c) =>
      val i = StdProvider.freshTemp()
      (i, Seq(Presburger.Var[Either[String, Int]](Left(i)) === Presburger.Const(c.toInt)))
    case _ => throw new MatchError("abstractA: argument is neither a variable nor numeral: " + a)
  }

  object Length extends IntValuedOperation {
    case class Lang(lenVar: String) extends ParikhLanguage[Char, String] {
      def usedAlphabet = Set.empty

      def toParikhAutomaton(alphabet: Set[Char]) =
        ParikhAutomaton(
          Set(0),
          alphabet,
          Set(0),
          Set(lenVar),
          alphabet.map(a => (0, a, Map(0 -> 1), 0)),
          0,
          Set((0, Map(0 -> 0))),
          Seq(Presburger.Eq(Presburger.Var(Left(lenVar)), Presburger.Var(Right(0))))
        )
    }

    def extractThis: PartialFunction[Terms.Term, (String, String, Lang)] = {
      case Strings.Length(SimpleQualID(x)) =>
        val l = StdProvider.freshTemp()
        (l, x, Lang(l)) // l == Length(x) under x \in Lang(l)
    }
  }

  object CountChar extends IntValuedOperation {
    case class Lang(charNum: String, targetChar: Char) extends ParikhLanguage[Char, String] {
      def usedAlphabet: Set[Char] = Set(targetChar)
      def toParikhAutomaton(alphabet: Set[Char]): ParikhAutomaton[Int, Char, Int, String] =
        ParikhAutomaton(
          states = Set(0),
          inSet = alphabet,
          ls = Set(0),
          is = Set(charNum),
          edges = alphabet
            .filterNot(_ == targetChar)
            .map(a => (0, a, Map(0 -> 0), 0)) + ((0, targetChar, Map(0 -> 1), 0)),
          q0 = 0,
          acceptRelation = Set((0, Map(0 -> 0))),
          acceptFormulas = Seq(Presburger.Eq(Presburger.Var(Left(charNum)), Presburger.Var(Right(0))))
        )
    }

    def extractThis = {
      case Strings.CountChar(SimpleQualID(name), Terms.SString(w)) if w.length == 1 =>
        val charNum = StdProvider.freshTemp()
        (charNum, name, Lang(charNum, w(0)))
    }
  }

  object IndexOf extends IntValuedOperation {

    sealed trait Lang extends ParikhLanguage[Char, String]

    // (= j (str.indexof x w c)) --> IndexOfConst(w, c, j)
    case class IndexOfConst(target: Seq[Char], from: Int, jName: String) extends Lang {
      def usedAlphabet: Set[Char] = target.toSet

      override def toParikhAutomaton(alphabet: Set[Char]): ParikhAutomaton[Int, Char, Int, String] = {
        import Presburger._
        type L = Int
        type T = Term[Either[String, L]]
        val j: T = Var(Left(jName))
        val input: T = Var(Right(0))
        val untilMatch: T = Var(Right(1))
        type Q = Int
        type Edges = Iterable[(Q, Char, Map[L, Int], Q)]
        val dfa = postfixDFA(target, alphabet)
        val skipStates = (-from to -1).toSet
        val skipEdges = for {
          q <- skipStates
          a <- alphabet
        } yield (q, a, Map(0 -> 1, 1 -> 1), q + 1)
        val skipOutGraph = skipStates.map(q => (q, Map(0 -> 0, 1 -> 0)))
        val states = dfa.states
        val edges: Edges = {
          for {
            q <- states
            a <- alphabet
          } yield {
            val r = dfa.transition.getOrElse((q, a), q)
            val skipped =
              if (dfa.finalStates(r)) 0
              else q + 1 - r
            val v = Map(0 -> 1, 1 -> skipped)
            (q, a, v, r)
          }
        }
        val outGraph =
          // On each state q, DFA has partially matched prefix of target string.
          states.map(q => (q, Map(0 -> 0, 1 -> (q % target.length))))
        val acceptFormulas = Seq(
          (input < from || input <= untilMatch) ==> (j === -1),
          (input >= from && input > untilMatch) ==> (j === untilMatch)
        )
        ParikhAutomaton[Q, Char, L, String](
          states ++ skipStates,
          alphabet,
          Set(0, 1),
          Set(jName),
          edges.toSet ++ skipEdges,
          -from,
          outGraph ++ skipOutGraph,
          acceptFormulas
        )
      }
    }

    // (= j (str.indexof x w i)) --> x ∈ IndexOf(w, i, j)
    case class IndexOf(target: Seq[Char], idxTerm: Terms.Term, jName: String) extends Lang {
      def usedAlphabet: Set[Char] = target.toSet

      def toParikhAutomaton(alphabet: Set[Char]): ParikhAutomaton[Int, Char, Int, String] = {
        import Presburger._
        type L = Int
        type T = Term[Either[String, L]]
        val (iName, binding) = abstractA(idxTerm)
        val i: T = Var(Left(iName))
        val j: T = Var(Left(jName))
        val input: T = Var(Right(0))
        val untilMatch: T = Var(Right(1))
        val skipped: T = Var(Right(2))
        type Q = Int
        type Edges = Iterable[(Q, Char, Map[L, Int], Q)]
        val dfa = postfixDFA(target, alphabet)
        val states = dfa.states
        val edges: Edges = {
          for {
            q <- states
            a <- alphabet
          } yield {
            val r = dfa.transition.getOrElse((q, a), q)
            val skipped =
              if (dfa.finalStates(r)) 0
              else q + 1 - r
            val v = Map(0 -> 1, 1 -> skipped, 2 -> 0)
            (q, a, v, r)
          }
        }
        val outGraph =
          // On each state q, DFA has partially matched prefix of target string.
          states.map(q => (q, Map(0 -> 0, 1 -> (q % target.length), 2 -> 0)))
        val acceptFormulas = binding ++ Seq(
          (i < 0 || input <= i) ==> (j === -1),
          (i >= 0 && i < input) ==> (skipped === i),
          (input <= untilMatch) ==> (j === -1),
          (input > untilMatch) ==> (j === untilMatch)
        )
        val skipState = -1
        val fromSkipState = {
          val trans = graphToMap(edges) { case (q, a, v, r) => (q, a) -> (r, v) }
          alphabet.flatMap { a =>
            trans(dfa.q0, a).map { case (r, v) => (skipState, a, v + (2 -> 0), r) } +
              ((skipState, a, Map(0 -> 1, 1 -> 1, 2 -> 1), skipState))
          }
        }
        ParikhAutomaton[Q, Char, L, String](
          states + skipState,
          alphabet,
          Set(0, 1, 2),
          Set(iName, jName),
          edges.toSet ++ fromSkipState,
          skipState,
          outGraph + ((skipState, Map(0 -> 0, 1 -> 0, 2 -> 0))),
          acceptFormulas
        )
      }
    }

    override def extractThis: PartialFunction[Terms.Term, (String, String, Lang)] = {
      case Strings.IndexOf(SimpleQualID(name), Terms.SString(w), Terms.SNumeral(c)) if c >= 0 =>
        val newVar = StdProvider.freshTemp()
        (newVar, name, IndexOfConst(w, c.toInt, newVar))
      case Strings.IndexOf(SimpleQualID(name), Terms.SString(w), t) =>
        val j = StdProvider.freshTemp()
        (j, name, IndexOf(w, t, j))
    }

  }

  object CodeAt extends IntValuedOperation {

    case class Lang(idxTerm: Terms.Term, cName: String) extends ParikhLanguage[Char, String] {
      def usedAlphabet: Set[Char] = Set.empty
      def toParikhAutomaton(alphabet: Set[Char]): ParikhAutomaton[Int, Char, Int, String] = {
        import Presburger._
        val (q0, qf) = (0, 1)
        val (iName, binding) = abstractA(idxTerm)
        type T = Term[Either[String, Int]]
        val (i, c): (T, T) = (Var(Left(iName)), Var(Left(cName)))
        val (input, index, code): (T, T, T) = (Var(Right(0)), Var(Right(1)), Var(Right(2)))
        ParikhAutomaton(
          Set(q0, qf),
          alphabet,
          Set(0, 1, 2),
          Set(iName, cName),
          alphabet.flatMap { a =>
            Iterable(
              (q0, a, Map(0 -> 1, 1 -> 1, 2 -> 0), q0),
              (q0, a, Map(0 -> 1, 1 -> 0, 2 -> a.toInt), qf),
              (qf, a, Map(0 -> 1, 1 -> 0, 2 -> 0), qf)
            )
          },
          q0,
          Set((q0, Map(0 -> 0, 1 -> 0, 2 -> -1)), (qf, Map(0 -> 0, 1 -> 0, 2 -> 0))),
          binding ++ Seq(
            (i >= 0 && i < input) ==> (i === index && c === code),
            (i < 0 || input <= i) ==> (c === -1)
          )
        )
      }
    }

    override def extractThis: PartialFunction[Terms.Term, (String, String, Lang)] = {
      case Strings.CodeAt(SimpleQualID(name), i) =>
        val c = StdProvider.freshTemp()
        (c, name, Lang(i, c))
    }

  }
}

sealed trait StringValuedOperation extends Operation {
  override def rangeSort: Terms.Sort = Strings.StringSort()
  def expectString: PartialFunction[Terms.Term, Nothing]
}

object StringValuedOperation {
  val builtins: Seq[StringValuedOperation] = Seq(
    )
}
