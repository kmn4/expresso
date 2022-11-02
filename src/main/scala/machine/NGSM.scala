package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso.math.{Cop, Cop1, Cop2, Monoid}
import com.github.kmn4.expresso.{graphToMap, searchStates, UpdateOps}

case class NGSM[Q, A, B](
    states: Set[Q],
    inSet: Set[A],
    edges: Set[(Q, A, Seq[B], Q)],
    q0: Q,
    outGraph: Set[(Q, Seq[B])]
) {

  type M = Seq[B]
  lazy val monoid: Monoid[M] = Monoid.seqMonoid
  lazy val outF: Map[Q, Set[M]] = graphToMap(outGraph)(identity)

  private lazy val trans: Map[(Q, A), Set[(Q, M)]] = graphToMap(edges) {
    case (q, a, bs, r) => (q, a) -> (r, bs)
  }

  def transOne(q: Q, a: A): Set[(Q, M)] = trans((q, a))
  def outputAt(q: Q, m: M): Set[M] = outF(q).map(mf => implicitly[Monoid[M]].combine(m, mf))
  def transition(qs: Set[Q], w: Seq[A]): Set[(Q, M)] = Monoid.transition(qs, w, transOne)
  def transduce(w: Seq[A]): Set[M] =
    transition(Set(q0), w).flatMap { case (q, m) => outputAt(q, m) }


  def andThenNSST[R, C, X](that: NSST[R, B, C, X]): NSST[(Q, R), A, C, X] = {
    val (newStates, newEdges) = searchStates(Set((q0, that.q0)), inSet) {
      case ((q1, r1), a) =>
        for {
          (q2, w) <- transOne(q1, a)
          (r2, m) <- that.transition(Set(r1), w.toList)
        } yield ((q2, r2), m)
    }(_._1, { case (q, a, (r, m)) => (q, a, m, r) })
    val newOutGraph = for {
      qr @ (q, r) <- newStates
      w <- outF(q)
      (r2, update) <- that.transition(Set(r), w.toList)
      xcs <- that.outF(r2)
    } yield (qr, update.subst(xcs))
    val newOutF = graphToMap(newOutGraph)(identity)
    NSST(
      newStates,
      inSet,
      that.variables,
      newEdges,
      (q0, that.q0),
      newOutF
    )
  }

  private def lift(bs: Seq[B]): Map[Unit, List[Cop[Unit, B]]] =
    Map(() -> (Cop1(()) +: bs.map(Cop2.apply)).toList)
  def toNSST: NSST[Q, A, B, Unit] = NSST(
    states,
    inSet,
    Set(()),
    edges.map(e => e.copy(_3 = lift(e._3))),
    q0,
    graphToMap(outGraph) { case (q, bs) => q -> lift(bs)(()) }
  )
}

case class ParikhNGSM[Q, A, B, L](
    states: Set[Q],
    inSet: Set[A],
    ls: Set[L],
    edges: Set[(Q, A, Seq[B], Map[L, Int], Q)],
    q0: Q,
    outGraph: Set[(Q, Seq[B], Map[L, Int])]
) {
  private def lift(bs: Seq[B]): Map[Unit, List[Cop[Unit, B]]] =
    Map(() -> (Cop1(()) +: bs.map(Cop2.apply)).toList)
  def toParikhSST[I]: ParikhSST[Q, A, B, Unit, L, I] = ParikhSST(
    states,
    inSet,
    Set(()),
    ls,
    Set.empty,
    edges.map(e => e.copy(_3 = lift(e._3))),
    q0,
    outGraph.map(o => o.copy(_2 = lift(o._2)(()))),
    Seq.empty
  )
}
