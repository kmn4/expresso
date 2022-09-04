package com.github.kmn4.expresso.machine

import com.github.kmn4.expresso
import com.github.kmn4.expresso.math.Presburger.{Var, Formula => PresFormula}

/** D はデータドメイン、I は入力シンボル、O は出力シンボル。
  */
abstract class StreamingDataStringTransducer[D, I, O] protected {

  // abstract members

  type State
  type DataVar
  type ListVar

  val types: DatastringTransducerTypes[I, O, State, ListVar, DataVar]
  import types._

  // WARN: be careful when overriding the following `def`s.
  //   otherwise an exception may be thrown during evaluation of `require`s below.
  def states: Set[State]
  def inputTags: Set[InputTag]
  def outputTags: Set[OutputTag]
  def dataVars: Set[DataVar]
  def listVars: Set[ListVar]
  def curr: DataVar
  def transitions: Set[Edge]
  def initialStates: Set[State]
  def outputRelation: Set[(State, ListSpec)]

  // 匿名クラス構文 new StreamingDataStringTransducer { ... } によってインスタンスを生成するとき、
  // 上記の def を val で実装すると、states == null などとなった状態で以下の require が評価され例外が送出される。
  // { ... } に記述する内容が、このクラスのコンストラクタより前に評価されればよくて、
  // そのために early initialization という機構が Scala 2.12 まではあったのだが、Scala 2.13 で deprecated となり、
  // Scala 3 でドロップされた。
  // 残された回避方法として lazy val やサブクラスでのパラメトリックフィールド化がある。
  // 参考:
  //   https://docs.scala-lang.org/tutorials/FAQ/initialization-order.html
  //   https://docs.scala-lang.org/scala3/reference/other-new-features/trait-parameters.html
  require(listVars.nonEmpty, "set of list variables should contain at least one element") // 実装上都合がいい
  require(dataVars(curr), "the current data variable must be an element of listVars")
  require(
    outputRelation.forall(o => !outputSpecOf(o).dataVariables.contains(curr)),
    "output specification cannot use the current data variable"
  )
  require(outputRelation.forall(o => outputSpecOf(o).isCopyless), "output specification must be copyless")
  require(transitions.forall(e => updateOf(e).isCopyless), "any update must be copyless")
  require(outputRelation.map(stateOf) subsetOf states, "states where output is defined must be in states")
  require(
    transitions.flatMap(e => Set(srcOf(e), dstOf(e))) subsetOf states,
    "source and destination of any transition must be in states"
  )

  // concrete members

  def stateOf(o: (State, ListSpec)): State         = o._1
  def outputSpecOf(o: (State, ListSpec)): ListSpec = o._2

  def srcOf(e: Edge): State     = e._1
  def updateOf(e: Edge): Update = e._4
  def dstOf(e: Edge): State     = e._5

  private val _edgesTo: collection.mutable.Map[State, Set[Edge]] = collection.mutable.Map()
  def edgesTo(q: State): Set[Edge] = _edgesTo.getOrElseUpdate(q, transitions.filter(dstOf(_) == q))
}

abstract class SimpleStreamingDataStringTransducer[D] extends StreamingDataStringTransducer[D, Unit, Unit] {
  type DataVar = Unit
  lazy val inputTags: Set[types.InputTag]   = Set(())
  lazy val outputTags: Set[types.OutputTag] = Set(())
  lazy val dataVars: Set[DataVar]           = Set(())
  lazy val curr: DataVar                    = ()
}

object SimpleStreamingDataStringTransducer { outer =>

  trait SimpleDatastringTypes[X] extends DatastringTypes[Unit, X, Unit]
  trait SimpleDatastringTransducerTypes[Q, X] extends DatastringTransducerTypes[Unit, Unit, Q, X, Unit] {
    type SimpleEdge = (State, Update, State)

    def curr: DataVar                                   = ()
    def itag: InputTag                                  = ()
    def otag: OutputTag                                 = ()
    def SimpleDataVar(x: DataVar): SymAndVar            = DataVar(otag, x)
    def SimpleUpdate(u: (ListVar, ListSpec)*): Update   = (Map.from(u), Map())
    def SimpleEdge(p: State, u: Update, q: State): Edge = (p, itag, noguard, u, q)
  }

  abstract class Factory[D, Q, X] private {
    val types: SimpleDatastringTransducerTypes[Q, X]
    def apply(
        states: Set[Q],
        listVars: Set[X],
        transitions: Set[types.Edge],
        initialStates: Set[Q],
        outputRelation: Set[(Q, types.ListSpec)]
    ): SimpleStreamingDataStringTransducer[D]
  }

  private object Factory {
    def apply[D, Q, X]() = new Factory[D, Q, X] { factory =>
      val types = new SimpleDatastringTransducerTypes[Q, X] {}
      import types._
      def apply(
          states: Set[Q],
          listVars: Set[X],
          transitions: Set[Edge],
          initialStates: Set[Q],
          outputRelation: Set[(Q, ListSpec)]
      ): SimpleStreamingDataStringTransducer[D] = new SimpleStreamingDataStringTransducerImpl(types)(
        states,
        listVars,
        transitions,
        initialStates,
        outputRelation,
      )

      // ここで states や types などをパラメトリックフィールドにしないと、
      // StreamingDataStringTransducer の require でコケる (isCopyless とかが使えないから)
      class SimpleStreamingDataStringTransducerImpl(val types: factory.types.type)(
          val states: Set[Q],
          val listVars: Set[X],
          val transitions: Set[Edge],
          val initialStates: Set[Q],
          val outputRelation: Set[(Q, ListSpec)],
      ) extends SimpleStreamingDataStringTransducer[D] {
        type State   = Q
        type ListVar = X
      }
    }
  }

  def factory[D, Q, X]: Factory[D, Q, X] = Factory()

  // make set of initial states singleton
  def canonicalize[D](s: SimpleStreamingDataStringTransducer[D]): SimpleStreamingDataStringTransducer[D] = {
    if (s.initialStates.size == 1) return s
    val factory = SimpleStreamingDataStringTransducer.factory[D, Option[s.types.State], s.types.ListVar]
    import factory.types.{SimpleEdge}
    factory(
      states = s.states.map(Option.apply) + None,
      listVars = s.listVars,
      transitions = {
        val fromNone =
          s.transitions
            .withFilter(s.initialStates contains s.srcOf(_))
            .map(e => SimpleEdge(Option.empty, s.updateOf(e), Option(s.dstOf(e))))
        val wrapped =
          s.transitions.map(e => SimpleEdge(Option(s.srcOf(e)), s.updateOf(e), Option(s.dstOf(e))))
        fromNone ++ wrapped
      },
      initialStates = Set(None),
      outputRelation = {
        val atNone =
          s.outputRelation
            .withFilter(s.initialStates contains s.stateOf(_))
            .map(o => Option.empty -> s.outputSpecOf(o))
        val wrapped = s.outputRelation
          .map(o => Option(s.stateOf(o)) -> s.outputSpecOf(o))
        atNone ++ wrapped
      }
    )
  }

  // exmaples

  def reverse[D]: SimpleStreamingDataStringTransducer[D] = {
    case object q // for state
    case object x // for list variable

    val factory = SimpleStreamingDataStringTransducer.factory[D, q.type, x.type]
    import factory.types._
    factory(
      states = Set(q),
      listVars = Set(x),
      transitions = Set(SimpleEdge(q, SimpleUpdate((x, ListSpec(SimpleDataVar(curr), ListVar(x)))), q)),
      initialStates = Set(q),
      outputRelation = Set(q -> ListSpec(ListVar(x)))
    )
  }

  def identity[D]: SimpleStreamingDataStringTransducer[D] = {
    case object q
    case object x
    val factory = SimpleStreamingDataStringTransducer.factory[D, q.type, x.type]
    import factory.types._
    factory(
      states = Set(q),
      listVars = Set(x),
      transitions = Set(SimpleEdge(q, SimpleUpdate((x, ListSpec(ListVar(x), SimpleDataVar(curr)))), q)),
      initialStates = Set(q),
      outputRelation = Set(q -> ListSpec(ListVar(x)))
    )
  }

  def duplicate[D]: SimpleStreamingDataStringTransducer[D] = {
    case object q
    object ListVarEnum extends Enumeration { val x, y = Value }
    import ListVarEnum.{x, y, Value => X}
    val factory = SimpleStreamingDataStringTransducer.factory[D, q.type, X]
    import factory.types._
    factory(
      states = Set(q),
      listVars = Set(x, y),
      transitions = {
        def id(z: X) = z -> ListSpec(ListVar(z), SimpleDataVar(curr))
        Set(SimpleEdge(q, SimpleUpdate(id(x), id(y)), q))
      },
      initialStates = Set(q),
      outputRelation = Set(q -> ListSpec(ListVar(x), ListVar(y)))
    )
  }

  def reverseIdentity1[D]: SimpleStreamingDataStringTransducer[D] = {
    case object q
    case object x
    val factory = SimpleStreamingDataStringTransducer.factory[D, q.type, x.type]
    import factory.types._
    factory(
      states = Set(q),
      listVars = Set(x),
      transitions = Set(
        SimpleEdge(q, SimpleUpdate((x, ListSpec(SimpleDataVar(curr), ListVar(x), SimpleDataVar(curr)))), q)
      ),
      initialStates = Set(q),
      outputRelation = Set(q -> ListSpec(ListVar(x)))
    )
  }

  def reverseIdentity2[D]: SimpleStreamingDataStringTransducer[D] = {
    case object q
    object ListVarEnum extends Enumeration { val x, y = Value }
    import ListVarEnum.{x, y, Value => X}
    val factory = SimpleStreamingDataStringTransducer.factory[D, q.type, X]
    import factory.types._
    factory(
      states = Set(q),
      listVars = Set(x, y),
      transitions = {
        def id(z: X)  = z -> ListSpec(ListVar(z), SimpleDataVar(curr))
        def rev(z: X) = z -> ListSpec(SimpleDataVar(curr), ListVar(z))
        Set(SimpleEdge(q, SimpleUpdate(rev(x), id(y)), q))
      },
      initialStates = Set(q),
      outputRelation = Set(q -> ListSpec(ListVar(x), ListVar(y)))
    )
  }

  def reverseIdentity3[D]: SimpleStreamingDataStringTransducer[D] = {
    case object q
    object ListVarEnum extends Enumeration { val x, y, z = Value }
    import ListVarEnum.{x, y, z, Value => X}
    val factory = SimpleStreamingDataStringTransducer.factory[D, q.type, X]
    import factory.types._
    factory(
      states = Set(q),
      listVars = Set(x, y, z),
      transitions = {
        def id(z: X)  = z -> ListSpec(ListVar(z), SimpleDataVar(curr))
        def rev(z: X) = z -> ListSpec(SimpleDataVar(curr), ListVar(z))
        Set(SimpleEdge(q, SimpleUpdate(rev(x), id(y), id(z)), q))
      },
      initialStates = Set(q),
      outputRelation = Set(q -> ListSpec(ListVar(x), ListVar(y)))
    )
  }

  private def singleStateConstructionScheme[D](): SimpleStreamingDataStringTransducer[D] = ???
}

trait DatastringTypes[O, X, V] {
  type OutputTag = O
  type ListVar   = X
  type DataVar   = V
  type SymAndVar = Either[ListVar, (OutputTag, DataVar)]
  object ListVar {
    def apply(x: X): SymAndVar           = Left(x)
    def unapply(x: SymAndVar): Option[X] = x.left.toOption
  }
  object DataVar {
    def apply(o: O, x: V): SymAndVar          = Right((o, x))
    def unapply(x: SymAndVar): Option[(O, V)] = x.toOption
  }
  implicit class SymAndVarOps(z: SymAndVar) {
    def listVarOption: Option[X]      = ListVar.unapply(z)
    def dataVarOption: Option[(O, V)] = DataVar.unapply(z)
  }
  val isListVar = (x: SymAndVar) => x.listVarOption.nonEmpty
  val isDataVar = (x: SymAndVar) => x.dataVarOption.nonEmpty

  type ListSpec = Seq[SymAndVar]
  object ListSpec {
    def apply(xs: SymAndVar*): ListSpec = Seq(xs: _*)
  }
  implicit class ListSpecOps(self: ListSpec) {
    def listVariables: Seq[X] = self.flatMap(_.listVarOption)
    def dataVariables: Seq[V] = self.flatMap(_.dataVarOption.map(_._2))

    def isCopyless: Boolean = noDuplicate(listVariables)
  }
  val emptySpec: ListSpec = Seq.empty

  type ListUpdate = Map[X, ListSpec]
  type DataUpdate = Map[V, V]
  type Update     = (ListUpdate, DataUpdate)
  val ListUpdate = Map
  implicit class ListUpdateOps(self: ListUpdate) {
    def listVariablesUsedInRHS: Set[X] = self.values.flatMap(_.listVariables).toSet
    def isCopyless: Boolean = {
      val listVariables: Seq[X] = self.values.toSeq.flatMap(_.listVariables)
      noDuplicate(listVariables)
    }
  }
  implicit class DataUpdateOps(self: DataUpdate) {
    def isCopyless: Boolean = noDuplicate(self.values.toSeq)
  }
  implicit class UpdateOps(self: Update) {
    def listUpdate: ListUpdate = self._1
    def dataUpdate: DataUpdate = self._2

    def isCopyless: Boolean            = listUpdate.isCopyless && dataUpdate.isCopyless
    def listVariablesUsedInRHS: Set[X] = listUpdate.listVariablesUsedInRHS
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

trait DatastringTransducerTypes[I, O, Q, X, V] extends DatastringTypes[O, X, V] {
  type Edge     = (State, InputTag, Guard, Update, State)
  type State    = Q
  type InputTag = Unit
  def noguard: Guard = new Guard {}
}

/** `D` は少なくとも2つの値を持つ。 `one != two` である必要がある。
  */
trait AtLeastTwo[D] {
  def one: D
  def two: D
}

object AtLeastTwo {
  implicit val booleanAL2 = new AtLeastTwo[Boolean] {
    def one: Boolean = true
    def two: Boolean = false
  }
}

object DataStringTheoryExamples extends App {
  type D = Boolean
  val theory = new DataStringTheory[D]
  import theory.{checkEquivalenceSimple, checkFunctionalitySimple, composeSimple}
  import SimpleStreamingDataStringTransducer.{
    reverse,
    identity,
    duplicate,
    reverseIdentity1,
    reverseIdentity2,
    reverseIdentity3,
  }
  assert(checkEquivalenceSimple(reverse, reverse))
  assert(!checkEquivalenceSimple(reverse, identity))
  assert(checkFunctionalitySimple(duplicate))
  assert(checkFunctionalitySimple(reverseIdentity1))
  assert(checkEquivalenceSimple(reverseIdentity1, reverseIdentity2))
  assert(checkEquivalenceSimple(reverseIdentity1, reverseIdentity3))
  assert(!checkEquivalenceSimple(duplicate, reverseIdentity1))
  assert(checkEquivalenceSimple(composeSimple(reverse, reverse), identity))
  println("examples done")
}

// checkEquivalenceSimple が健全であるために `AtLeastTwo` が必要。
class DataStringTheory[D: AtLeastTwo] {
  type SSDT = SimpleStreamingDataStringTransducer[D]

  def asSST(s: SSDT): NSST[_, Unit, Unit, _] = {
    val t: SSDT = SimpleStreamingDataStringTransducer.canonicalize(s)
    import t.types._
    import expresso.math.{Cop, Cop1, Cop2}
    import expresso.{Cupstar, Update => SstUpdate}
    def trL(e: ListSpec): Cupstar[ListVar, Unit] = e.toList.map {
      case ListVar(x)    => Cop1(x)
      case DataVar(_, _) => Cop2(())
      case _             => throw new IllegalStateException("this cannot happen")
    }
    def trU(u: Update): SstUpdate[ListVar, Unit] = u.listUpdate.map { case (x, w) => x -> trL(w) }
    NSST[t.State, Unit, Unit, ListVar](
      t.states,
      Set(()),
      t.listVars,
      t.transitions.map(e => (t.srcOf(e), (), trU(t.updateOf(e)), t.dstOf(e))),
      t.initialStates.head,
      expresso.graphToMap(t.outputRelation) { case (q, w) => q -> trL(w) }
    )
  }
  def asSSDT[Q, X](t: NSST[Q, Unit, Unit, X]): SSDT = {
    val factory = SimpleStreamingDataStringTransducer.factory[D, Q, X]
    import factory.types._
    import expresso.math.{Cop1, Cop2}
    def trU(u: expresso.Update[X, Unit]): Update =
      SimpleUpdate(u.toSeq.map { case (x, w) => x -> trW(w) }: _*)
    def trW(w: expresso.Cupstar[X, Unit]): ListSpec = w.map {
      case Cop1(x) => ListVar(x)
      case Cop2(_) => DataVar(otag, curr)
    }
    factory(
      t.states,
      t.variables,
      t.edges.map { case (p, _, update, q) => SimpleEdge(p, trU(update), q) },
      Set(t.q0),
      (for ((q, w) <- t.outGraph) yield (q -> trW(w))).toSet
    )
  }
  def composeSimple(t1: SSDT, t2: SSDT): SSDT    = asSSDT(asSST(t1) compose asSST(t2))
  def checkFunctionalitySimple(t: SSDT): Boolean = checkEquivalenceSimple(t, t)
  def checkEquivalenceSimple(t1: SSDT, t2: SSDT): Boolean = {
    import expresso.math.Presburger.Sugar._

    def notEquiv = differByDomain || differByLength || differAtSomePosition

    def differByDomain: Boolean = false // TODO: 実装するか、全域性を要求する
    def differByLength: Boolean = {
      val toParikhAutomaton = parikhAutomatonConstructionScheme(endOfOutput) _
      // TODO: Parikh 拡張を入れる場合、ji, pi は toParikhAutomaton が自動生成して返す
      def p = toParikhAutomaton(t1, "j1", "p1") intersect toParikhAutomaton(t2, "j2", "p2")
      p.addFormula(Var("p1") !== Var("p2")).internal.ilVectorOption.nonEmpty
    }
    def differAtSomePosition: Boolean = {
      // 結果の PA が w を受理するなら、t に w を与えるとその j 文字目が出力の "p" 文字目に現れる
      val toParikhAutomaton = parikhAutomatonConstructionScheme(someInternalPosition) _
      def p                 = toParikhAutomaton(t1, "j1", "p1") intersect toParikhAutomaton(t2, "j2", "p2")
      p.addFormula((Var("j1") !== Var("j2")) && (Var("p1") === Var("p2"))).internal.ilVectorOption.nonEmpty
    }
    sealed trait Position
    case object someInternalPosition extends Position
    case object endOfOutput          extends Position
    // 結果の Parikh オートマトンが w を受理するとする。
    // t に w を入力として与えたときの出力を w' とすると、w' の位置 p は w の j 文字目である。
    // ただし、出力の終端も「文字」であると考える；w' の位置 w'.length は、w の w.length 文字目である。
    def parikhAutomatonConstructionScheme(
        pPointsTo: Position
    )(t: SSDT, j: String, p: String): SimplePA[String] = {
      val types = new DatastringTypes[Unit, t.ListVar, t.DataVar] {}
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
      def Label(x: Label): Var[Either[String, Label]] = Var(Right(x))
      def I(x: String): Var[Either[String, Label]]    = Var(Left(x))

      val labels    = Set(lj, lp)
      val intParams = Set(j, p)
      val formula   = Label(lj) === I(j) && Label(lp) === I(p)
      val isInitial = (q: t.State, f: Guess) => t.initialStates(q) && !f.pGuessed
      lazy val finals: Set[(t.State, Guess)] = t.outputRelation flatMap { case (state, outputSpec) =>
        val x      = t.listVars.head
        val xs     = t.listVars - x
        val update = xs.map(_ -> emptySpec) + (x -> outputSpec)
        val relativeToP = pPointsTo match {
          case `endOfOutput`          => `left`
          case `someInternalPosition` => `center`
        }
        val guess = xs.map(_ -> (unused: LRCU)) + (x -> relativeToP)
        prevGuesses(Guess.from(guess), ListUpdate.from(update)) map ((state, _))
      }
      lazy val (states, edges) = expresso.searchStates(finals, Set(())) { case ((r, g), _) =>
        t.edgesTo(r) flatMap { e =>
          val p      = t.srcOf(e)
          val update = t.updateOf(e).listUpdate
          def res: Iterable[(t.State, Map[Label, Int], Guess)] = prevGuesses(g, update) map { f =>
            def res = (p, Map(lj -> e, lp -> c), f)
            def e   = if (g.pGuessed) 0 else 1
            def c   = t.listVars.iterator.map(cIn).sum
            def cIn(x: t.ListVar): Int = g(x) match {
              case `left`             => update(x).filter(isDataVar).length
              case `right` | `unused` => 0
              case `center` if !f.pGuessed =>
                val w1 = update(x).takeWhile(z => !(z.listVarOption.map(f) == Some(right)))
                w1.filter(isDataVar).length - 1
              case `center` =>
                val w = update(x)
                (0 until w.length)
                  .collectFirst(w.splitAt(_) match {
                    case (w1, ListVar(y) +: _) if f(y) == center => w1.filter(isDataVar).length
                  })
                  .get
            }
            res
          }
          res
        }
      }(
        c => (c._1, c._3),
        { case ((r, g), _, (p, u, f)) => ((p, f), (), u, (r, g)) }
      )

      def prevGuesses(guess: Guess, update: ListUpdate): Iterable[Guess] = {
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
                  case DataVar(_, _) =>
                    w1.listVariables.map(_ -> left) ++ w2.listVariables.map(_ -> right)
                  case _ =>
                    throw new IllegalStateException(
                      "this should not be the case: all SymAndVar is either ListVar or DataVar"
                    )
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
          params = Set(j, p),
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

abstract class SimplePA[I] { outer =>
  type State
  type Label
  val internal: ParikhAutomaton[State, Unit, Label, I]
  def intersect(that: SimplePA[I]): SimplePA[I] = new SimplePA[I] {
    type State = (outer.State, that.State)
    type Label = expresso.math.Cop[outer.Label, that.Label]
    val internal = outer.internal intersect that.internal
  }
  def addFormula(f: PresFormula[I]): SimplePA[I] = new SimplePA[I] {
    type State = outer.State
    type Label = outer.Label
    val internal = {
      val orig                              = outer.internal
      val fm: PresFormula[Either[I, Label]] = f.renameVars(Left.apply)
      orig.copy(acceptFormulas = fm +: orig.acceptFormulas)
    }
  }
}

object SimplePA {

  // 拡張したのは、今のところ初期状態が複数ありうるということだけ
  case class ExtendedSyntax[Q, L, I](
      states: Set[Q],
      labels: Set[L],
      params: Set[I],
      edges: Set[(Q, Unit, Map[L, Int], Q)],
      initialStates: Set[Q],
      acceptRelation: Set[(Q, Map[L, Int])],
      acceptFormulae: Seq[PresFormula[Either[I, L]]]
  )

  def from[Q, L, I](spec: ExtendedSyntax[Q, L, I]): SimplePA[I] = new SimplePA[I] {
    type State = Option[Q]
    type Label = L
    val internal = {
      val states = spec.states.map(Option(_)) + None
      val edges = {
        val fromNone =
          for ((p, a, v, q) <- spec.edges if spec.initialStates(p)) yield (Option.empty[Q], a, v, Option(q))
        val wrapped = spec.edges.map { case (p, a, v, q) => (Option(p), a, v, Option(q)) }
        wrapped ++ fromNone
      }
      val acceptRelation = {
        spec.acceptRelation.withFilter(o => spec.initialStates(o._1)).map(o => (None, o._2)) ++
          spec.acceptRelation.map(o => (Option(o._1), o._2))
      }
      ParikhAutomaton(
        states = states,
        inSet = Set(()),
        ls = spec.labels,
        is = spec.params,
        edges = edges,
        q0 = None,
        acceptRelation = acceptRelation,
        acceptFormulas = spec.acceptFormulae
      )
    }
  }

}
