package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso.math.{Cop, Cop1, Cop2, Presburger}
import com.github.kmn4.expresso.{graphToMap, searchStates}

case class ParikhAutomaton[Q, A, L, I](
    states: Set[Q],
    inSet: Set[A],
    ls: Set[L],
    is: Set[I],
    edges: Set[(Q, A, ParikhSST.ParikhUpdate[L], Q)],
    q0: Q,
    acceptRelation: Set[(Q, Map[L, Int])],
    acceptFormulas: Seq[Presburger.Formula[Either[I, L]]]
) {

  // Require that all vectors be positive.
  // This will not change expressivenes
  //  and might make satisfiability checking simpler.
  require(edges.forall { case (_, _, v, _) => v.forall { case (_, n) => n >= 0 } })

  lazy val sizes = (states.size, edges.size)

  val trans      = graphToMap(edges) { case (q, a, v, r) => (q, a) -> (r, v) }
  val acceptFunc = graphToMap(acceptRelation) { case (q, v) => q -> v }

  lazy val acceptF = graphToMap(acceptRelation)(identity)

  lazy val psst                                   = toParikhSST
  def accept(iv: Map[I, Int])(s: Seq[A]): Boolean = psst.transduce(s, iv).nonEmpty

  def intersect[R, K](that: ParikhAutomaton[R, A, K, I]): ParikhAutomaton[(Q, R), A, Cop[L, K], I] = {
    type FS = Seq[Presburger.Formula[Either[I, Cop[L, K]]]]
    val newQ0 = (q0, that.q0)
    def vecCoproduct(v: Map[L, Int], u: Map[K, Int]): Map[Cop[L, K], Int] = {
      val lkv = v.map { case (l, n) => Cop1[L, K](l) -> n }
      val lku = u.map { case (k, n) => Cop2[L, K](k) -> n }
      (lkv ++ lku).toMap
    }
    def nextStates(qr: (Q, R), a: A): Set[((Q, R), Map[Cop[L, K], Int])] = {
      val (q, r) = qr
      for {
        (qq, v) <- trans(q, a)
        (rr, u) <- that.trans(r, a)
      } yield ((qq, rr), vecCoproduct(v, u))
    }
    val (newStates, newEdges) = searchStates(Set(newQ0), inSet)(nextStates)(
      _._1,
      { case (qr, a, (qqrr, v)) => (qr, a, v, qqrr) }
    )
    val newAccRel = for {
      (q, r) <- newStates
      v      <- acceptFunc(q)
      u      <- that.acceptFunc(r)
    } yield ((q, r), vecCoproduct(v, u))
    val newFormulas: FS = {
      val thisFs: FS = acceptFormulas.map(_.renameVars(_.map(Cop1.apply)))
      val thatFs: FS = that.acceptFormulas.map(_.renameVars(_.map(Cop2.apply)))
      thisFs ++ thatFs
    }
    ParikhAutomaton(
      newStates,
      inSet ++ that.inSet,
      ls.map(Cop1.apply) ++ that.ls.map(Cop2.apply),
      is ++ that.is,
      newEdges,
      newQ0,
      newAccRel,
      newFormulas
    )
  }

  /** Returns a pair (n, v) of I vector and L vector that meets the following if exists: there exists w for
    * which this outputs v and formula(n, v) == true.
    */
  def ilVectorOption: Option[(Map[I, Int], Map[L, Int])] = toParikhSST.ilVectorOption

  def renamed: ParikhAutomaton[Int, A, Int, I] = {
    val qMap = states.zipWithIndex.toMap
    // 束縛変数の付け替えをするには、ls.zipWithIndex.toMap では足りない
    val lMap = new com.github.kmn4.expresso.math.Renamer[L]
    ParikhAutomaton(
      states.map(qMap),
      inSet,
      ls.map(lMap),
      is,
      edges.map { case (q, a, v, r) => (qMap(q), a, v.map { case (l, n) => lMap(l) -> n }, qMap(r)) },
      qMap(q0),
      acceptRelation.map { case (q, v) => (qMap(q), v.map { case (l, n) => lMap(l) -> n }) },
      acceptFormulas.map(_.renameVars(_.map(lMap)))
    )
  }

  def toIdentityParikhSST: ParikhSST[Q, A, A, Unit, L, I] = {
    val x      = List[Cop[Unit, A]](Cop1(()))
    val update = inSet.map(a => a -> Map(() -> List(Cop1(()), Cop2(a)))).toMap
    ParikhSST(
      states,
      inSet,
      Set(()),
      ls,
      is,
      edges.map { case (q, a, v, r) => (q, a, update(a), v, r) },
      q0,
      acceptRelation.map { case (q, v) => (q, x, v) },
      acceptFormulas
    )
  }

  def toParikhSST: ParikhSST[Q, A, Nothing, Nothing, L, I] = ParikhSST[Q, A, Nothing, Nothing, L, I](
    states,
    inSet,
    Set.empty,
    ls,
    is,
    edges.map { case (q, a, v, r) => (q, a, Map.empty, v, r) },
    q0,
    acceptRelation.map { case (q, v) => (q, List.empty, v) },
    acceptFormulas
  )

  def ignoreFormulas: NFA[Q, A] = new NFA(
    states,
    inSet,
    graphToMap(edges) { case (q, a, v, r) => (q, Some(a)) -> r },
    q0,
    acceptRelation.map(_._1)
  )
}

object ParikhAutomaton {
  def universal[Q, A, L, I](q: Q, inSet: Set[A]): ParikhAutomaton[Q, A, L, I] =
    DFA.universal(q, inSet).toParikhAutomaton
}
