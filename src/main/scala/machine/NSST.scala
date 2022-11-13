package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.math._

/** Nondeterministic streaming string transducer */
case class NSST[Q, A, B, X](
    states: Set[Q],
    in: Set[A],
    variables: Set[X],
    edges: Set[(Q, A, Update[X, B], Q)],
    q0: Q,
    partialF: Map[Q, Set[Cupstar[X, B]]]
) {
  import NSST._

  implicit val monoid: Monoid[Update[X, B]] = updateMonoid(variables)
  val outF: Map[Q, Set[Cupstar[X, B]]] = partialF.withDefaultValue(Set())
  val outGraph: List[(Q, Cupstar[X, B])] = mapToGraph(partialF)(identity).toList

  val delta: Map[(Q, A), Set[(Q, Update[X, B])]] =
    graphToMap(edges) { case (q, a, m, r) => (q, a) -> ((r, m)) }

  def transOne(q: Q, a: A): Set[(Q, Update[X, B])] = delta.withDefaultValue(Set.empty)((q, a))
  def transition(qs: Set[Q], w: List[A]): Set[(Q, Update[X, B])] =
    Monoid.transition(qs, w, (q: Q, a: A) => transOne(q, a))
  def outputAt(q: Q, m: Update[X, B]): Set[List[B]] =
    outF(q).map { flatMap1(_, m) }.map(erase1)
  def transduce(w: Seq[A]): Set[List[B]] =
    transition(Set(q0), w.toList).flatMap { case (q, m) => outputAt(q, m) }

  def copyfulEdge = edges.find { case (_, _, m, _) => !isCopylessUpdate(m) }
  def copyfulOutF = outF.find { case (_, s)        => s.exists(!isCopylessOutput(_)) }
  def copyfulWitness = copyfulEdge ++ copyfulOutF
  def copyfulWitnessOpt = (copyfulEdge ++ copyfulOutF).headOption
  def isCopyless: Boolean = copyfulWitness.isEmpty

  def isEmpty: Boolean = {
    val reachables = closure(
      Set(q0),
      graphToMap(edges) { case (q, _, _, r) => q -> r }
    )
    (reachables intersect partialF.filter { case (_, s) => s.nonEmpty }.map(_._1).toSet).isEmpty
  }

  def renamed: NSST[Int, A, B, Int] = {
    val stateMap = (states zip LazyList.from(0)).toMap
    val varMap = (variables zip LazyList.from(0)).toMap
    def renameXbs(xbs: Cupstar[X, B]): Cupstar[Int, B] = xbs.map(_.map1(varMap))
    val newEdges =
      edges
        .flatMap {
          case (q, a, m, r) if states.contains(q) && states.contains(r) =>
            Some((stateMap(q), a, m.map { case (x, xbs) => varMap(x) -> renameXbs(xbs) }, stateMap(r)))
          case _ => None
        }
    val newF = partialF.map { case (q, s) => (stateMap(q), s.map(renameXbs)) }
    NSST(
      stateMap.map(_._2).toSet,
      in,
      varMap.map(_._2).toSet,
      newEdges,
      stateMap(q0),
      newF
    )
  }

  /** Construct NSST that transduce w to that.transduce(this.transduce(w)). */
  def compose[R, C, Y](that: NSST[R, B, C, Y]): NSST[Int, A, C, Int] = {
    this.copyfulWitnessOpt map (w => throw new Exception(s"Tried to compose NSST, but first NSST was copyfull: ${w}"))
    that.copyfulWitnessOpt map (w => throw new Exception(s"Tried to compose NSST, but second NSST was copyfull: ${w}"))
    val p = this.toParikhSST[Nothing, Nothing] compose that.toParikhSST[Nothing, Nothing]
    NSST(
      p.states,
      p.inSet,
      p.xs,
      p.edges.map { case (q, a, m, _, r) => (q, a, m, r) },
      p.q0,
      graphToMap(p.outGraph) { case (q, xbs, _) => q -> xbs }
    )
  }

  def toParikhSST[L, I](ls: Set[L]): ParikhSST[Q, A, B, X, L, I] = ParikhSST(
    states,
    in,
    variables,
    ls,
    Set.empty,
    edges.map { case (q, a, m, r) => (q, a, m, ls.map(_ -> 0).toMap, r) },
    q0,
    outGraph.map { case (q, xbs) => (q, xbs, ls.map(_ -> 0).toMap) }.toSet,
    Seq.empty
  )

  def toParikhSST[L, I]: ParikhSST[Q, A, B, X, L, I] = toParikhSST(Set.empty)
}

object NSST {
  type Edge[Q, A, B, X] = (Q, A, Update[X, B], Q)
  type Edges[Q, A, B, X] = Set[Edge[Q, A, B, X]]
  type Out[Q, X, B] = (Q, Cupstar[X, B])
  def isCopylessUpdate[X, B](update: Update[X, B]): Boolean = {
    val vars = update.keySet
    def count(x: X): Int = update.foldLeft(0) {
      case (acc, (_, rhs)) =>
        acc + rhs.foldLeft(0) {
          case (acc, Cop1(y)) if y == x => acc + 1
          case (acc, _)                 => acc
        }
    }
    vars.forall(count(_) <= 1)
  }
  def isCopylessOutput[X, A](output: Cupstar[X, A]): Boolean = {
    output
      .foldLeft((true, Set[X]())) {
        case ((b, s), Cop1(x)) => (b || s.contains(x), s + x)
        case ((b, s), Cop2(a)) => (b, s)
      }
      ._1
  }

  def apply(
      states: Iterable[Int],
      vars: Iterable[Char],
      edges: Iterable[(Int, Char, Iterable[(Int, Iterable[String])])],
      q0: Int,
      outF: Iterable[(Int, String)]
  ): NSST[Int, Char, Char, Char] = {
    def stringToCupstar(s: String): Cupstar[Char, Char] =
      s.map[Cop[Char, Char]] { c => if (c.isUpper) Cop1(c) else Cop2(c) }.toList
    def stringsToUpdate(ss: Iterable[String]): Update[Char, Char] =
      ss.map(s => s.head -> stringToCupstar(s.substring(2))).toMap
    val newEdges =
      edges
        .flatMap { case (q, a, s) => s.map { case (r, m) => (q, a, stringsToUpdate(m), r) } }
    val newF = outF.map { case (q, s) => q -> Set(stringToCupstar(s)) }.toMap
    NSST(
      states.toSet,
      edges.map(_._2).toSet,
      vars.toSet,
      newEdges.toSet,
      q0,
      newF
    )
  }
}
