package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso.machine._

/** グループ変数 X で添字付けられたキャプチャグループの括弧 */
private sealed trait Paren[X]
private case class LPar[X](x: X) extends Paren[X]
private case class RPar[X](x: X) extends Paren[X]

sealed trait PCRE[A, X] {
  private[language] type ParsedChar = Either[A, Paren[X]]
  private[language] type Parsed = Seq[ParsedChar]

  def usedChars: Set[A] = this match {
    case PCRE.Chars(as)                             => as
    case PCRE.Cat(e1, e2)                           => e1.usedChars ++ e2.usedChars
    case PCRE.Alt(e1, e2)                           => e1.usedChars ++ e2.usedChars
    case PCRE.Greedy(e)                             => e.usedChars
    case PCRE.NonGreedy(e)                          => e.usedChars
    case PCRE.Group(e, _)                           => e.usedChars
    case PCRE.GDeriv(e, _)                          => e.usedChars
    case PCRE.Empty() | PCRE.Eps() | PCRE.AllChar() => Set.empty
  }

  private[language] def groupVarTrees: Seq[Tree[X]] = this match {
    case PCRE.Empty() | PCRE.Eps() | PCRE.Chars(_) | PCRE.AllChar() => Seq.empty
    case PCRE.Cat(e1, e2)                                           => e1.groupVarTrees ++ e2.groupVarTrees
    case PCRE.Alt(e1, e2)                                           => e1.groupVarTrees ++ e2.groupVarTrees
    case PCRE.Greedy(e)                                             => e.groupVarTrees
    case PCRE.NonGreedy(e)                                          => e.groupVarTrees
    case PCRE.Group(e, x)                                           => Seq(Tree(x, e.groupVarTrees: _*))
    case PCRE.GDeriv(e, x)                                          => Seq(Tree(x, e.groupVarTrees: _*))
  }

  def groupVars: Set[X] = groupVarTrees.flatMap(_.toSeq).toSet

  override def toString(): String = this match {
    case PCRE.Empty() => "∅"
    case PCRE.Eps()   => ""
    case PCRE.Chars(as) =>
      as.size match {
        case 0 => "[∅]"
        case 1 => as.head.toString()
        case _ => s"[${as.mkString}]"
      }
    case PCRE.AllChar()   => "."
    case PCRE.Cat(e1, e2) => s"$e1$e2"
    case PCRE.Alt(e1, e2) => s"$e1|$e2"
    case PCRE.Greedy(e) =>
      val s = e.toString()
      if (s.length == 1) s"$e*"
      else s"($e)*"
    case PCRE.NonGreedy(e) =>
      val s = e.toString()
      if (s.length == 1) s"$e*?"
      else s"($e)*?"
    case PCRE.Group(e, x)  => s"(?<$x>$e)"
    case PCRE.GDeriv(e, x) => s"<?<$x>$e>"
  }

  def renameVars[Y](f: X => Y): PCRE[A, Y] = this match {
    case PCRE.Group(e, x)  => PCRE.Group(e.renameVars(f), f(x))
    case PCRE.GDeriv(e, x) => PCRE.GDeriv(e.renameVars(f), f(x))
    case PCRE.Empty()      => PCRE.Empty()
    case PCRE.Eps()        => PCRE.Eps()
    case PCRE.Chars(as)    => PCRE.Chars(as)
    case PCRE.AllChar()    => PCRE.AllChar()
    case PCRE.Cat(e1, e2)  => PCRE.Cat(e1.renameVars(f), e2.renameVars(f))
    case PCRE.Alt(e1, e2)  => PCRE.Alt(e1.renameVars(f), e2.renameVars(f))
    case PCRE.Greedy(e)    => PCRE.Greedy(e.renameVars(f))
    case PCRE.NonGreedy(e) => PCRE.NonGreedy(e.renameVars(f))
  }
}

object PCRE {
  case class Empty[A, X]() extends PCRE[A, X]
  case class Eps[A, X]() extends PCRE[A, X]
  case class Chars[A, X](as: Set[A]) extends PCRE[A, X]
  case class Cat[A, X](e1: PCRE[A, X], e2: PCRE[A, X]) extends PCRE[A, X]
  case class Alt[A, X](e1: PCRE[A, X], e2: PCRE[A, X]) extends PCRE[A, X]
  case class Greedy[A, X](e: PCRE[A, X]) extends PCRE[A, X]
  case class NonGreedy[A, X](e: PCRE[A, X]) extends PCRE[A, X]
  case class Group[A, X](e: PCRE[A, X], x: X) extends PCRE[A, X]
  // Derivatives of group expressions.
  case class GDeriv[A, X](e: PCRE[A, X], x: X) extends PCRE[A, X]
  case class AllChar[A, X]() extends PCRE[A, X]
}
