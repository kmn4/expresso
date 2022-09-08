package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso
import com.github.kmn4.expresso.math.Presburger.{Var, Formula => PresFormula}
import com.github.kmn4.expresso.math.Cop1
import com.github.kmn4.expresso.math.Cop2

sealed trait CurrOrDelim
object CurrOrDelim {
  case object curr  extends CurrOrDelim
  case object delim extends CurrOrDelim
}

trait DatastringTypes2[X] {
  type ListVar   = X
  type VarOrChar = expresso.math.Cop[ListVar, CurrOrDelim]
  val ListVar   = expresso.math.Cop1
  val Character = expresso.math.Cop2
  val curr      = CurrOrDelim.curr
  val delim     = CurrOrDelim.delim
  implicit class VarOrCharOps(z: VarOrChar) {
    // def listVarOption: Option[X] = ListVar.unapply(z)
    def listVarOption: Option[X] = z match {
      case ListVar(a)   => Some(a)
      case Character(b) => None
    }
  }
  val isListVar = (x: VarOrChar) => x.listVarOption.nonEmpty

  type ListSpec = Seq[VarOrChar]
  object ListSpec {
    def apply(xs: VarOrChar*): ListSpec = Seq(xs: _*)
  }
  implicit class ListSpecOps(self: ListSpec) {
    def listVariables: Seq[X] = self.flatMap(_.listVarOption)

    def isCopyless: Boolean = noDuplicate(listVariables)
  }
  val emptySpec: ListSpec = Seq.empty

  type Update = Map[X, ListSpec]
  val Update = Map
  implicit class UpdateOps(self: Update) {
    def listVariablesUsedInRHS: Set[X] = self.values.flatMap(_.listVariables).toSet
    def isCopyless: Boolean = {
      val listVariables: Seq[X] = self.values.toSeq.flatMap(_.listVariables)
      noDuplicate(listVariables)
    }
  }

  sealed trait Guard

  private def noDuplicate[A](xs: Seq[A]): Boolean = {
    def aux(xs: Seq[A], acc: Set[A]): Boolean = xs match {
      case Nil     => true
      case x +: xs => !acc(x) && aux(xs, acc + x)
    }
    aux(xs, Set())
  }
}

abstract class SimpleStreamingDataStringTransducer2 {
  type State
  type ListVar
  def internalSST: NSST[State, CurrOrDelim, CurrOrDelim, ListVar]

  import CurrOrDelim._

  type ListSpec = List[expresso.math.Cop[ListVar, CurrOrDelim]]
  val emptySpec: ListSpec = Nil

  type Update = expresso.Update[ListVar, CurrOrDelim]
  type Edge   = (State, CurrOrDelim, Update, State)
  val transitions                                  = internalSST.edges
  val initialStates                                = Set(internalSST.q0)
  val outputRelation                               = internalSST.outGraph.toSet
  val listVars                                     = internalSST.variables
  def srcOf(e: Edge): State                        = e._1
  def dstOf(e: Edge): State                        = e._4
  def inputOf(e: Edge): CurrOrDelim                = e._2
  def updateOf(e: Edge): Update                    = e._3
  def stateOf(o: (State, ListSpec)): State         = o._1
  def outputSpecOf(o: (State, ListSpec)): ListSpec = o._2
  val ListVar                                      = expresso.math.Cop1
  val Character                                    = expresso.math.Cop2

  private val _edgesTo: collection.mutable.Map[State, Set[Edge]] = collection.mutable.Map()
  def edgesTo(q: State): Set[Edge] = _edgesTo.getOrElseUpdate(q, transitions.filter(dstOf(_) == q))

  // 入力がデータ (resp. #) な遷移の更新では curr (resp. #) しか使わない。
  require(transitions.map(e => (inputOf(e), updateOf(e))).forall {
    case (`curr`, u) =>
      u.forall { case (_, output) =>
        output.forall {
          case ListVar(_)        => true
          case Character(`curr`) => true
          case _                 => false
        }
      }
    case (`delim`, u) =>
      u.forall { case (_, output) =>
        output.forall {
          case ListVar(_)         => true
          case Character(`delim`) => true
          case _                  => false
        }
      }
  })
  // 少なくとも１つのリスト変数を持つ（そうでなければ空列しか返せないので）
  require(listVars.nonEmpty)
}

object SimpleStreamingDataStringTransducer2 {
  def apply[Q, X](internalSST: NSST[Q, CurrOrDelim, CurrOrDelim, X]): SimpleStreamingDataStringTransducer2 =
    new SimpleStreamingDataStringTransducer2Impl[Q, X](internalSST)
  private class SimpleStreamingDataStringTransducer2Impl[Q, X](
      val internalSST: NSST[Q, CurrOrDelim, CurrOrDelim, X]
  ) extends SimpleStreamingDataStringTransducer2 {
    type State   = Q
    type ListVar = X
  }

  def from1[D](t: SimpleStreamingDataStringTransducer[D]): SimpleStreamingDataStringTransducer2 = {
    import CurrOrDelim._
    val canon = SimpleStreamingDataStringTransducer.canonicalize(t)
    def convSpec(w: canon.types.ListSpec): expresso.Cupstar[canon.ListVar, CurrOrDelim] = w.map {
      case Left(x)  => Cop1(x)
      case Right(_) => Cop2(curr)
    }.toList
    def convUpdate(u: canon.types.Update): expresso.Update[canon.ListVar, CurrOrDelim] = u._1 map {
      case (x, w) => x -> convSpec(w)
    }
    SimpleStreamingDataStringTransducer2(
      NSST[canon.State, CurrOrDelim, CurrOrDelim, canon.ListVar](
        states = canon.states,
        in = Set(curr, delim),
        variables = canon.listVars,
        edges = canon.transitions map { case e =>
          val u = canon.updateOf(e)
          (canon.srcOf(e), curr, convUpdate(u), canon.dstOf(e))
        },
        q0 = canon.initialStates.head,
        partialF = expresso.graphToMap(canon.outputRelation) { case (state, spec) =>
          state -> convSpec(spec)
        }
      )
    )
  }

  import CurrOrDelim._
  val theory1          = new DataStringTheory[Boolean]
  def reverse          = from1(SimpleStreamingDataStringTransducer.reverse)
  def identity         = from1(SimpleStreamingDataStringTransducer.identity)
  def duplicate        = from1(SimpleStreamingDataStringTransducer.duplicate)
  def reverseIdentity1 = from1(SimpleStreamingDataStringTransducer.reverseIdentity1)
  def reverseIdentity2 = from1(SimpleStreamingDataStringTransducer.reverseIdentity2)
  def reverseIdentity3 = from1(SimpleStreamingDataStringTransducer.reverseIdentity3)

}

object DataStringTheory2Examples extends App {
  import DataStringTheory2.{checkEquivalence, checkFunctionality, compose}
  import SimpleStreamingDataStringTransducer2.{
    reverse,
    identity,
    duplicate,
    reverseIdentity1,
    reverseIdentity2,
    reverseIdentity3,
  }
  assert(checkEquivalence(reverse, reverse))
  assert(!checkEquivalence(reverse, identity))
  assert(checkFunctionality(duplicate))
  assert(checkFunctionality(reverseIdentity1))
  assert(checkEquivalence(reverseIdentity1, reverseIdentity2))
  assert(checkEquivalence(reverseIdentity1, reverseIdentity3))
  assert(!checkEquivalence(duplicate, reverseIdentity1))
  assert(checkEquivalence(compose(reverse, reverse), identity))
  println("examples done")
}

object DataStringTheory2 {
  type SSDT = SimpleStreamingDataStringTransducer2
  val SSDT = SimpleStreamingDataStringTransducer2
  def compose(t1: SSDT, t2: SSDT): SSDT =
    SSDT(t1.internalSST compose t2.internalSST)
  def checkFunctionality(t: SSDT): Boolean = checkEquivalence(t, t)
  def checkEquivalence(t1: SSDT, t2: SSDT): Boolean = {
    import expresso.math.Presburger.Sugar._

    def notEquiv = differByDomain || differByLength || differAtSomePosition

    def differByDomain: Boolean = false // TODO: 実装するか、全域性を要求する
    def differByLength: Boolean = {
      val toParikhAutomaton = parikhAutomatonConstructionScheme(endOfOutput) _
      // TODO: Parikh 拡張を入れる場合、ji, pi は toParikhAutomaton が自動生成して返す
      def p =
        toParikhAutomaton(t1, "j1", "p1", "_1") intersect toParikhAutomaton(t2, "j2", "p2", "_2")
      p.addFormula(Var("p1") !== Var("p2")).internal.ilVectorOption.nonEmpty
    }
    def differAtSomePosition: Boolean = {
      // 結果の PA が w を受理するなら、t に w を与えるとその j 文字目が出力の "p" 文字目に現れる
      val toParikhAutomaton = parikhAutomatonConstructionScheme(someInternalPosition) _
      def p =
        toParikhAutomaton(t1, "j1", "p1", "isDelim1") intersect toParikhAutomaton(t2, "j2", "p2", "isDelim2")
      p.addFormula(
        // p1 == p2 && (isDelim1 != isDelim2 || (isDelim == 0 && j1 != j2))
        (Var("p1") === Var("p2")) &&
          ((Var("isDelim1") !== Var("isDelim2")) ||
            ((Var("isDelim1") === 0) && (Var("j1") !== Var("j2"))))
      ).internal
        .ilVectorOption
        .nonEmpty
    }
    sealed trait Position
    case object someInternalPosition extends Position
    case object endOfOutput          extends Position
    // 結果の Parikh オートマトンが w を受理するとする。
    // また、t に w を入力として与えたときの出力を w' とする。
    // isDelim == 1 のとき、w' の位置 p は区切り文字である。
    // そうでないとき、w' の位置 p は w の j 文字目である。
    // ただし、出力の終端も「文字」であると考える；w' の位置 w'.length は、w の w.length 文字目である。
    def parikhAutomatonConstructionScheme(
        pPointsTo: Position
    )(t: SSDT, j: String, p: String, isDelim: String): SimplePA[String] = {
      val types = new DatastringTypes2[t.ListVar] {}
      import types._

      trait LRCU         extends Product with Serializable
      case object left   extends LRCU
      case object right  extends LRCU
      case object center extends LRCU
      case object unused extends LRCU
      type Guess = Map[t.ListVar, LRCU]
      implicit class GuessOps(self: Guess) {
        // `pPointsTo == someInternalPosition` can be omitted, but is left for the sake of efficiency
        val pGuessed: Boolean = pPointsTo == someInternalPosition && self.exists(_._2 == center)
      }
      val Guess = Map

      trait Label    extends Product with Serializable
      case object lj extends Label
      case object lp extends Label
      case object ld extends Label
      def Label(x: Label): Var[Either[String, Label]] = Var(Right(x))
      def I(x: String): Var[Either[String, Label]]    = Var(Left(x))

      val labels    = Set(lj, lp, ld)
      val intParams = Set(j, p, isDelim)
      val formula   = Label(lj) === I(j) && Label(lp) === I(p) && Label(ld) === I(isDelim)
      val isInitial = (q: t.State, f: Guess) => t.initialStates(q) && !f.pGuessed
      lazy val finals: Set[(t.State, Guess)] = t.outputRelation flatMap { case (state, outputSpec) =>
        val x      = t.listVars.head
        val xs     = t.listVars - x
        val update = xs.map(_ -> t.emptySpec) + (x -> outputSpec)
        val relativeToP = pPointsTo match {
          case `endOfOutput`          => `left`
          case `someInternalPosition` => `center`
        }
        val guess = xs.map(_ -> (unused: LRCU)) + (x -> relativeToP)
        prevGuesses(Guess.from(guess), Update.from(update)) map ((state, _))
      }
      lazy val (states, edges) = expresso.searchStates(finals, Set(())) { case ((r, g), _) =>
        t.edgesTo(r) flatMap { e =>
          val p      = t.srcOf(e)
          val update = t.updateOf(e)
          val input  = t.inputOf(e)
          def res: Iterable[(t.State, Map[Label, Int], Guess)] = prevGuesses(g, update) map { f =>
            def res = (p, Map(lj -> e, lp -> c, ld -> (if (splittedAtDelim) 1 else 0)), f)
            def e   = if (g.pGuessed) 0 else 1
            def c   = t.listVars.iterator.map(cIn).sum
            def cIn(x: t.ListVar): Int = g(x) match {
              case `left`             => update(x).filter(a => !isListVar(a)).length
              case `right` | `unused` => 0
              case `center` if !f.pGuessed =>
                val w1 = update(x).takeWhile(z => !(z.listVarOption.map(f) == Some(right)))
                w1.filter(a => !isListVar(a)).length - 1
              case `center` =>
                val w = update(x)
                (0 until w.length)
                  .collectFirst(w.splitAt(_) match {
                    case (w1, t.ListVar(y) +: _) if f(y) == center =>
                      w1.filter(!isListVar(_)).length
                  })
                  .get
            }
            def splittedAtDelim: Boolean = !f.pGuessed && g.pGuessed && input == delim
            // def splittedAtDelim: Boolean = !f.pGuessed &&
            //   t.listVars
            //     .find(x => g(x) == center)
            //     .map { x =>
            //       // cIn の case `center` if !f.pGuessed のコードのコピペ
            //       val w1 = update(x).takeWhile(z => !(z.listVarOption.map(f) == Some(right)))
            //       update(x)(w1.length) == Character(delim)
            //     }
            //     .getOrElse(false)
            res
          }
          res
        }
      }(
        c => (c._1, c._3),
        { case ((r, g), _, (p, u, f)) => ((p, f), (), u, (r, g)) }
      )

      def prevGuesses(guess: Guess, update: t.Update): Iterable[Guess] = {
        def candidates(x: t.ListVar): Iterable[Iterable[(t.ListVar, LRCU)]] =
          guess(x) match {
            case `left` | `right` | `unused` => Seq(update(x).listVariables.map(_ -> guess(x)))
            case `center` =>
              val w = update(x)
              (0 until w.length) map { i =>
                val (w1, z +: w2) = w.splitAt(i)
                z match {
                  case ListVar(z) =>
                    w1.listVariables.map(_ -> left) ++
                      ((z -> center) +: w2.listVariables.map(_ -> right))
                  case Character(_) =>
                    w1.listVariables.map(_ -> left) ++ w2.listVariables.map(_ -> right)
                }
              }
          }
        def constraints   = t.listVars map (x => candidates(x))
        def specsForUsed  = choices(constraints).map(_.flatten)
        def unusedInRHS   = t.listVars -- update.listVariablesUsedInRHS
        def specForUnused = unusedInRHS.map(_ -> unused)
        specsForUsed.map(s => s ++ specForUnused).map(Guess.from(_))
      }
      def choices[A](xss: Iterable[Iterable[A]]): Iterable[Seq[A]] =
        if (xss.isEmpty) Iterable(Seq())
        else {
          val xs  = xss.head
          val rec = choices(xss.tail)
          for {
            hd <- xs
            ys <- rec
          } yield hd +: ys
        }

      SimplePA.from(
        SimplePA.ExtendedSyntax[(t.State, Guess), Label, String](
          states = states,
          labels = labels,
          params = Set(j, p, isDelim),
          edges = edges,
          initialStates = states.filter { case (q, f) => isInitial(q, f) },
          acceptRelation = finals.map { q =>
            val zeroVector = Map(lj -> 0, lp -> 0)
            ((q, zeroVector))
          },
          acceptFormulae = Seq(formula)
        )
      )
    }

    !notEquiv
  }

}
