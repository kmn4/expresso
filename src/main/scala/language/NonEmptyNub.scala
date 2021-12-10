package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.machine._
import com.github.kmn4.expresso.math.MonadPlus.MonadPlusOps
import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso.Cupstar
import com.github.kmn4.expresso.Cupstar

trait NonEmptyNub[A] {
  def map[B](f: A => B): NonEmptyNub[B]
  def flatMap[B](f: A => Seq[B]): Option[NonEmptyNub[B]]
  def head: A
  def tail: Seq[A]
  def init: Seq[A]
  def last: A
  def toSeq: Seq[A]

  override def hashCode(): Int = toSeq.hashCode()

  override def equals(x: Any): Boolean = {
    x != null &&
    getClass() == x.getClass() &&
    toSeq == x.asInstanceOf[NonEmptyNub[A]].toSeq
  }

  override def toString(): String = toSeq.toString()
}

object NonEmptyNub {
  private class VectorNonEmptyNub[A](v: Vector[A]) extends NonEmptyNub[A] {

    override def map[B](f: A => B): NonEmptyNub[B] = new VectorNonEmptyNub(v.map(f).distinct)

    override def flatMap[B](f: A => Seq[B]): Option[NonEmptyNub[B]] = {
      val vv = v.flatMap(f)
      Option.when(vv.nonEmpty)(new VectorNonEmptyNub(vv.distinct))
    }

    override def head: A = v.head

    override def tail: Seq[A] = v.tail

    override def init: Seq[A] = v.init

    override def last: A = v.last

    override def toSeq: Seq[A] = v
  }

  def apply[A](head: A, tail: Seq[A]): NonEmptyNub[A] = new VectorNonEmptyNub(
    Vector.from(head +: tail).distinct
  )

  def InitLast[A]: PartialFunction[NonEmptyNub[A], (Seq[A], A)] = { case l: NonEmptyNub[A] =>
    (l.init, l.last)
  }
}
