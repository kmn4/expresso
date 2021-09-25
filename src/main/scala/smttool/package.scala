package com.github.kmn4.expresso

import smtlib.trees.TreeTransformer
import smtlib.trees.PrePostTreeTransformer
import smtlib.trees.Terms.Term
import smtlib.trees.Terms.QualifiedIdentifier
import smtlib.trees.Terms.SSymbol
import smtlib.trees.Terms.SimpleIdentifier
import smtlib.trees.Terms.FunctionApplication
import smtlib.theories.Core
import smtlib.trees.Tree
import smtlib.trees.Terms
import smtlib.trees.SimpleTreeTransformer

package object smttool {
  val functionCollector = new TreeTransformer {
    type C = Unit
    type R = Set[String]
    override def combine(
        tree: Tree,
        context: Unit,
        results: Seq[Set[String]]
    ): Set[String] = {
      val opt = tree match {
        case SimpleApp(name, _) => Some(name)
        case _                  => None

      }
      results.toSet.flatten ++ opt
    }
  }
  def collect(f: Term => Seq[Term]): Term => Seq[Term] = t => {
    val s = f(t)
    if (s.isEmpty) Seq(t)
    else s.flatMap(collect(f))
  }
  val andToTerms = collect { t => Core.And.unapplySeq(t).getOrElse(Seq.empty) }
  class SubstTransformer(f: PartialFunction[Term, Term]) extends SimpleTreeTransformer {
    val g = f.orElse[Term, Term](identity(_))
    override def post(sort: Terms.Sort): Terms.Sort = sort
    override def post(term: Term): Term = g(term)
    override def pre(sort: Terms.Sort): Terms.Sort = sort
    override def pre(term: Term): Term = term
  }
  def subst(f: PartialFunction[Term, Term]): Term => Term = new SubstTransformer(f).transform _
  val elimDoubleNegation = subst { case Core.Not(Core.Not(t)) => t }
  val elimITE = subst {
    case Core.Equals(
        Core.ITE(t, Terms.SNumeral(n), Terms.SNumeral(m)),
        Terms.SNumeral(l)
        ) =>
      if (n == l && m == l) Core.True()
      else if (n == l) t
      else if (m == l) Core.Not(t)
      else Core.False()
  }
  val elimAt = subst {
    case Strings.At(w, i) =>
      Strings.Substring(w, i, Terms.SNumeral(BigInt(1)))
  }
  def compose[A](f: A => A*): A => A = f.foldLeft[A => A](identity) {
    case (acc, f) => acc andThen f
  }
  val simplify: Term => Term = compose(elimITE, elimDoubleNegation, elimAt)

  object SimpleQualID {
    def apply(name: String): QualifiedIdentifier =
      QualifiedIdentifier(SimpleIdentifier(SSymbol(name)), None)
    def unapply(term: Term): Option[String] = term match {
      case QualifiedIdentifier(SimpleIdentifier(SSymbol(name)), None) =>
        Some(name)
      case _ => None
    }
  }

  object SimpleApp {
    def apply(name: String, args: Term*): Term =
      FunctionApplication(SimpleQualID(name), args)
    def unapply(term: Term): Option[(String, Seq[Term])] = term match {
      case FunctionApplication(SimpleQualID(name), terms) => Some((name, terms))
      case _                                              => None
    }
  }

  /** (= symbol term) の形 */
  object SimpleAssignment {
    def apply(name: String, t: Term): Term = Core.Equals(SimpleQualID(name), t)
    def unapply(t: Term): Option[(String, Term)] = t match {
      case Core.Equals(SimpleQualID(name), t) => Some((name, t))
      case _                                  => None
    }
  }

  // TODO (str.++ w_1 w_2) など
  object StringConst {
    def unapply(term: Term): Option[String] = term match {
      case Terms.SString(w) => Some(w)
      case _                => None
    }
  }

  // (str.contains x w) => (x, (re.++ re.all (str.to.re w) re.all))
  // (= x w) => (x, (str.to.re w))
  object RegexConstraint {
    def apply(term: Terms.Term, re: Term): Term =
      Strings.InRegex(term, re)
    def unapply(term: Term): Option[(Terms.Term, Term)] = term match {
      case Strings.InRegex(term, re) => Some((term, re))
      case Strings.Contains(t, StringConst(w)) =>
        val wre = Strings.ToRegex(Terms.SString(w))
        val re =
          Strings.Regex.Concat(Strings.Regex.All(), wre, Strings.Regex.All())
        Some((t, re))
      case Core.Equals(t, StringConst(w)) =>
        Some((t, Strings.ToRegex(Terms.SString(w))))
      case Strings.PrefixOf(StringConst(w), t) =>
        val re = Strings.Regex.Concat(
          Strings.ToRegex(Terms.SString(w)),
          Strings.Regex.All()
        )
        Some((t, re))
      case Core.Not(RegexConstraint(t, re)) => Some((t, Strings.Regex.Comp(re)))
      case _                                => None
    }
  }

  abstract class BottomUpTermTransformer extends PrePostTreeTransformer {

    type C = Unit

    def combine(results: Seq[R]): R

    final override def combine(tree: Tree, context: C, results: Seq[R]): R =
      combine(results)

    final override def pre(term: Term, context: C): (Term, C) = (term, context)

    final override def pre(sort: Terms.Sort, context: C): (Terms.Sort, C) =
      (sort, context)

    final override def post(sort: Terms.Sort, result: R): (Terms.Sort, R) =
      (sort, result)

  }

  abstract class TopDownTransformer extends PrePostTreeTransformer {
    type C = R

    def combine(results: Seq[R]): R

    final override def combine(tree: Tree, context: C, results: Seq[R]): R =
      combine(context +: results)

    final override def pre(sort: Terms.Sort, context: C): (Terms.Sort, C) =
      (sort, context)

    final override def post(sort: Terms.Sort, result: R): (Terms.Sort, R) =
      (sort, result)

    def post(term: Term, result: R): (Term, R) = (term, result)

  }
}
