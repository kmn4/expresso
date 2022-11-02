package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.machine._
import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso.math.MonadPlus.MonadPlusOps

private final case class Tree[A](a: A, children: Tree[A]*) {
  def toSeq: Seq[A] = a +: children.flatMap(_.toSeq)

  def toSet: Set[A] = toSeq.toSet
}

private object CompilePerlRegex {
  private[language] type ParsedChar[A, X] = Either[A, Paren[X]]
  private[language] type Parsed[A, X]     = Seq[ParsedChar[A, X]]

  private def derive[A, X, M[_]](
      a: A
  )(e: PCRE[A, X])(implicit mp: MonadPlus[M]): M[(Option[PCRE[A, X]], Parsed[A, X])] =
    e match {
      case PCRE.Empty()   => mp.empty
      case PCRE.Eps()     => mp((None, Seq.empty))
      case PCRE.Chars(as) => if (as(a)) mp.apply((Some(PCRE.Eps()), Seq(Left(a)))) else mp.empty
      case PCRE.AllChar() => mp.apply((Some(PCRE.Eps()), Seq(Left(a))))
      case PCRE.Cat(e1, e2) =>
        derive(a)(e1) >>= {
          case (Some(e), w) => mp((Some(PCRE.Cat(e, e2)), w))
          case (None, w)    => derive(a)(e2) >>= { case (e, u) => mp(e, w ++ u) }
        }
      case PCRE.Alt(e1, e2) => derive(a)(e1) ++ derive(a)(e2)
      case PCRE.Greedy(e) =>
        val derived =
          derive(a)(e) >>= {
            case (Some(f), w) => mp((Option(PCRE.Cat(f, PCRE.Greedy(e))), w))
            case (None, w)    => mp((None, w))
          }
        derived ++ mp((None, Seq.empty))
      case PCRE.NonGreedy(e) =>
        val derived =
          derive(a)(e) >>= {
            case (Some(f), w) => mp((Option(PCRE.Cat(f, PCRE.NonGreedy(e))), w))
            case (None, w)    => mp((None, w))
          }
        mp[(Option[PCRE[A, X]], Parsed[A, X])]((None, Seq.empty)) ++ derived
      case PCRE.Group(e, x) =>
        derive(a)(e) >>= {
          case (Some(e), w) => mp((Some(PCRE.GDeriv(e, x)), Right(LPar(x)) +: w))
          case (None, w)    => mp((None, Right(LPar(x)) +: w :+ Right(RPar(x))))
        }
      case PCRE.GDeriv(e, x) =>
        derive(a)(e) >>= {
          case (Some(e), w) => mp((Some(PCRE.GDeriv(e, x)), w))
          case (None, w)    => mp((None, w :+ Right(RPar(x))))
        }
    }

  private def matchOne[A, X, M[_]](e: PCRE[A, X], a: A)(implicit
      mp: MonadPlus[M]
  ): M[(PCRE[A, X], Parsed[A, X])] =
    derive(a)(e) >>= {
      case (Some(e), w) => mp((e, w))
      case (None, _)    => mp.empty
    }

  private def deriveEps[A, X, M[_]](e: PCRE[A, X])(implicit mp: MonadPlus[M]): M[Parsed[A, X]] = e match {
    case PCRE.Empty() | PCRE.Chars(_) | PCRE.AllChar() => mp.empty
    case PCRE.Eps()                                    => mp(Seq.empty)
    case PCRE.Cat(e1, e2)  => for (w <- deriveEps(e1); u <- deriveEps(e2)) yield w ++ u
    case PCRE.Alt(e1, e2)  => deriveEps(e1) ++ deriveEps(e2)
    case PCRE.Greedy(e)    => deriveEps(e) ++ mp(Seq.empty)
    case PCRE.NonGreedy(e) => mp(Seq.empty)
    case PCRE.Group(e, x)  => deriveEps(e).map(Right(LPar(x)) +: _ :+ Right(RPar(x)))
    case PCRE.GDeriv(e, x) => deriveEps(e).map(_ :+ Right(RPar(x)))
  }

  private[language] def toParser[A, X](
      e: PCRE[A, X],
      alphabet: Set[A]
  ): NGSM[NonEmptyNub[PCRE[A, X]], A, ParsedChar[A, X]] = {
    require(e.usedChars subsetOf alphabet)
    type Q = NonEmptyNub[PCRE[A, X]]
    val q0 = NonEmptyNub(e, Seq.empty)
    def nextStates(q: Q, a: A): Set[(Q, Parsed[A, X])] = {
      val lowest      = q.last
      val highers     = q.init
      val nextHighers = (highers >>= (matchOne(_, a))).map(_._1).distinct
      val nextLower   = matchOne(lowest, a).distinctBy(_._1)
      var nexts       = Set.empty[(Q, Parsed[A, X])]
      for (n <- 1 to nextLower.length if !nextHighers.contains(nextLower(n - 1)._1)) {
        val lowerExps = nextLower.take(n).map(_._1)
        val w         = nextLower(n - 1)._2
        val nextExps  = nextHighers ++ lowerExps
        val nextQ     = NonEmptyNub(nextExps.head, nextExps.tail)
        nexts += ((nextQ, w))
      }
      nexts
    }
    val (states, edges) = searchStates(Set(q0), alphabet)(nextStates)(
      { case (r, _) => r },
      { case (q, a, (r, w)) => (q, a, w, r) }
    )
    val outGraph = for {
      q <- states if q.init.forall(deriveEps(_).isEmpty)
      w <- deriveEps(q.last).headOption
    } yield q -> w
    NGSM(
      states,
      alphabet,
      edges,
      q0,
      outGraph
    )
  }

  def firstMatch[A, X](e: PCRE[A, X], alphabet: Set[A]): PCRE[A, Option[X]] = {
    val renamed: PCRE[A, Option[X]] = e.renameVars(x => Some(x))
    // .*?(e).*
    PCRE.Cat(
      PCRE.Cat(PCRE.NonGreedy(PCRE.Chars(alphabet)), PCRE.Group(renamed, None)),
      PCRE.Greedy(PCRE.Chars(alphabet))
    )
  }

  def repetitiveMatch[A, X](e: PCRE[A, X], alphabet: Set[A]): PCRE[A, Option[X]] = {
    val renamed: PCRE[A, Option[X]] = e.renameVars(x => Some(x))
    // (?:(e)|.)*
    PCRE.Greedy(PCRE.Alt(PCRE.Group(renamed, None), PCRE.Chars(alphabet)))
  }

  private type SSTQ[X] = Set[Option[X]]
  private sealed trait SSTVar[X]
  private case class Out[X]()                     extends SSTVar[X]
  private case class Rep[X](x: Option[X], i: Int) extends SSTVar[X]

  def replaceSST[A, X](
      re: PCRE[A, X],
      rep: Replacement[A, X],
      alphabet: Set[A]
  ): NSST[Int, A, A, Int] = {
    val repetitiveRE     = repetitiveMatch(re, alphabet)
    val repetitiveParser = toParser(repetitiveRE, alphabet)
    (repetitiveParser andThenNSST oneTimeReplaceSST(re, rep, alphabet)).renamed
  }

  def replaceAllSST[A, X](
      re: PCRE[A, X],
      rep: Replacement[A, X],
      alphabet: Set[A]
  ): NSST[Int, A, A, Int] = {
    val repetitiveRE     = repetitiveMatch(re, alphabet)
    val repetitiveParser = toParser(repetitiveRE, alphabet)
    (repetitiveParser andThenNSST repetitiveReplaceSST(re, rep, alphabet)).renamed
  }

  private def repetitiveReplaceSST[A, X](
      re: PCRE[A, X],
      rep: Replacement[A, X],
      alphabet: Set[A]
  ): NSST[SSTQ[X], ParsedChar[A, Option[X]], A, SSTVar[X]] = {
    require(rep.groupVars subsetOf re.groupVars)
    type UpdateVar = Update[SSTVar[X], A]
    type Edge      = (SSTQ[X], ParsedChar[A, Option[X]], UpdateVar, SSTQ[X])
    val repXs                      = rep.indexed.collect { case Right((x, i)) => Rep(x, i) }
    val sstVars: Set[SSTVar[X]]    = repXs.toSet + Out()
    val updates: Monoid[UpdateVar] = updateMonoid(sstVars)
    def aux(parent: SSTQ[X], varsTree: Tree[Option[X]]): (Set[SSTQ[X]], Set[Edge]) =
      varsTree match {
        case Tree(x, children @ _*) =>
          val cur = parent + x
          val newEdges: Set[Edge] = {
            val fromParen: Edge = {
              val shouldClear = repXs.filter { case Rep(y, i) => y == x }
              val update      = updates.unit ++ shouldClear.map(x => x -> Nil)
              (parent, Right(LPar(x)), update, cur)
            }
            val loops: Iterable[Edge] = {
              val shouldUpdate = repXs.filter { case Rep(y, i) => cur(y) }
              def update(a: A) = updates.unit ++ shouldUpdate.map(x => x -> List(Cop1(x), Cop2(a)))
              alphabet.map(a => (cur, Left(a), update(a), cur))
            }
            val toParent: Edge = {
              val zero: UpdateVar = sstVars.map(x => x -> Nil).toMap
              val update: UpdateVar = if (x == None) {
                val y = Cop1(Out[X]())
                val ys = rep.indexed.map {
                  case Right((x, i)) => Cop1(Rep(x, i))
                  case Left(a)       => Cop2(a)
                }
                zero + (Out() -> (y +: ys).toList)
              } else updates.unit
              (cur, Right(RPar(x)), update, parent)
            }
            loops.toSet + fromParen + toParent
          }
          val (childStates, childEdges) = children.foldLeft((Set.empty[SSTQ[X]], Set.empty[Edge])) {
            case ((accQ, accE), child) =>
              val (qs, es) = aux(cur, child)
              (accQ ++ qs, accE ++ es)
          }
          (childStates + cur, childEdges ++ newEdges)
      }
    val q0: SSTQ[X]     = Set.empty
    val repetitiveRE    = repetitiveMatch(re, alphabet)
    val varsTree        = repetitiveRE.groupVarTrees.head
    val (states, edges) = aux(q0, varsTree)
    val q0Loop: Iterable[Edge] = {
      def update(a: A): UpdateVar = updates.unit + (Out() -> List(Cop1(Out()), Cop2(a)))
      alphabet.map(a => (q0, Left(a), update(a), q0))
    }
    NSST[SSTQ[X], ParsedChar[A, Option[X]], A, SSTVar[X]](
      states + q0,
      varsTree.toSet.flatMap(x => Set(Right(LPar(x)), Right(RPar(x)))) ++ alphabet.map(Left.apply),
      sstVars,
      edges ++ q0Loop,
      q0,
      Map(q0 -> Set(List(Cop1(Out()))))
    )
  }
  // state Cop1(s): vars in s is opened, Cop2(false): initial state, Cop2(true): already replaced once
  private def oneTimeReplaceSST[A, X](
      re: PCRE[A, X],
      rep: Replacement[A, X],
      alphabet: Set[A]
  ): NSST[Cop[Set[Option[X]], Boolean], ParsedChar[A, Option[X]], A, SSTVar[X]] = {
    type Q = Cop[Set[Option[X]], Boolean]
    type U = Update[SSTVar[X], A]
    type E = (Q, ParsedChar[A, Option[X]], U, Q)
    val repetitive = repetitiveReplaceSST(re, rep, alphabet)
    val q0         = Cop2(false)
    val qf         = Cop2(true)
    val states     = repetitive.states.collect[Q] { case s if s.nonEmpty => Cop1(s) } + q0 + qf
    val unitUpdate = {
      val repXs = rep.indexed.collect { case Right((x, i)) => Rep(x, i) }
      updateMonoid[SSTVar[X], A](repXs.toSet + Out()).unit
    }
    val edges = repetitive.edges.map[E] {
      case (q, a @ Left(_), m, r) if q.isEmpty  => (q0, a, m, q0)
      case (q, x @ Right(_), m, r) if q.isEmpty => (q0, x, m, Cop1(r))
      case (q, a, m, r) if r.isEmpty            => (Cop1(q), a, m, qf)
      case (q, a, m, r)                         => (Cop1(q), a, m, Cop1(r))
    } ++ repetitive.in.collect[E] { // loop in qf
      case Left(a)  => (qf, Left(a), unitUpdate + (Out() -> List(Cop1(Out()), Cop2(a))), qf)
      case Right(p) => (qf, Right(p), unitUpdate + (Out() -> List(Cop1(Out()))), qf)
    }
    val out = List[Cop[SSTVar[X], A]](Cop1(Out()))
    repetitive.copy(
      states = states,
      edges = edges,
      q0 = q0,
      partialF = Map(q0 -> Set(out), qf -> Set(out))
    )
  }

}
