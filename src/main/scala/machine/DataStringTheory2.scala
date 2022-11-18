package com.github.kmn4.expresso.machine

import collection.mutable.{Map as MMap, Set as MSet}

import com.github.kmn4.expresso
import com.github.kmn4.expresso.Cupstar
import com.github.kmn4.expresso.math.Monoid
import com.github.kmn4.expresso.math.Presburger
import com.github.kmn4.expresso.math.{Cop1, Cop2, Cop}

enum CurrOrDelim { case curr, delim }

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
  type ParikhLabel
  def internalSST: ParikhSST[State, CurrOrDelim, CurrOrDelim, ListVar, ParikhLabel, String]

  import CurrOrDelim._

  type ListSpec = List[expresso.math.Cop[ListVar, CurrOrDelim]]
  val emptySpec: ListSpec = Nil

  type Update      = expresso.Update[ListVar, CurrOrDelim]
  type ParikhImage = Map[ParikhLabel, Int]
  type Edge        = (State, CurrOrDelim, Update, ParikhImage, State)
  type OutRel      = (State, ListSpec, ParikhImage)
  val transitions                           = internalSST.edges
  val initialStates                         = Set(internalSST.q0)
  val outputRelation                        = internalSST.outGraph.toSet
  val listVars                              = internalSST.xs
  val parikhLabels                          = internalSST.ls
  val intParams                             = internalSST.is
  val states                                = internalSST.states
  val initialState                          = internalSST.q0
  val acceptFormulae                        = internalSST.acceptFormulas
  def srcOf(e: Edge): State                 = e._1
  def dstOf(e: Edge): State                 = e._5
  def inputOf(e: Edge): CurrOrDelim         = e._2
  def updateOf(e: Edge): Update             = e._3
  def imageOf(e: Edge): ParikhImage         = e._4
  def stateOf(o: OutRel): State             = o._1
  def outputSpecOf(o: OutRel): ListSpec     = o._2
  def outputImageOf(o: OutRel): ParikhImage = o._3
  val ListVar                               = expresso.math.Cop1
  val Character                             = expresso.math.Cop2

  private val _edgesTo: MMap[State, Set[Edge]] = MMap()
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
  // Parikh像は非負である
  require(transitions.forall(imageOf(_).forall(_._2 >= 0)))

  require(transitions.map(updateOf).forall(update => update.keySet == listVars))
  require {
    val valuesListVars = for {
      update <- transitions.map(updateOf)
      (_, w) <- update
      sym    <- w
      x <- sym match {
        case Cop1(x) => Option(x)
        case Cop2(_) => Option.empty
      }
    } yield x
    valuesListVars subsetOf listVars
  }

  override def toString(): String =
    s"transitions=${transitions}" ++
      s"initialStates=${initialStates}" ++
      s"outputRelation=${outputRelation}" ++
      s"listVars=${listVars}" ++
      s"parikhLabels=${parikhLabels}" ++
      s"intParams=${intParams}" ++
      s"states=${states}" ++
      s"initialState=${initialState}" ++
      s"acceptFormulae=${acceptFormulae}"

}

object SimpleStreamingDataStringTransducer2 {
  def apply[Q, X, L](
      internalSST: ParikhSST[Q, CurrOrDelim, CurrOrDelim, X, L, String]
  ): SimpleStreamingDataStringTransducer2 {
    type State = Q; type ParikhLabel = L; type ListVar = X
  } =
    new SimpleStreamingDataStringTransducer2Impl[Q, X, L](internalSST)
  private class SimpleStreamingDataStringTransducer2Impl[Q, X, L](
      val internalSST: ParikhSST[Q, CurrOrDelim, CurrOrDelim, X, L, String]
  ) extends SimpleStreamingDataStringTransducer2 {
    type State       = Q
    type ListVar     = X
    type ParikhLabel = L
  }

  // 具体的なインスタンス

  private val sliceLabels @ Seq(seekedLabel, takenLabel, inputLabel) = Seq(0, 1, 2)

  import CurrOrDelim._

  def slice(begin: String, end: String): SimpleStreamingDataStringTransducer2 { type ParikhLabel = Int } = {
    val states @ Seq(seeking, taking, ignoring) = Seq(0, 1, 2)
    val listVar                                 = 0
    val labels @ Seq(seeked, taken, input)      = sliceLabels
    val (edges, outGraph) = {
      type Update = Map[Int, List[Cop[Int, CurrOrDelim]]]
      val id: Update  = Map(listVar -> List(Cop1(listVar)))
      val add: Update = Map(listVar -> List(Cop1(listVar), Cop2(curr)))
      def vec(sk: Int, tk: Int, in: Int): Map[Int, Int] =
        Map(seeked -> sk, taken -> tk, input -> in)
      // to `seeking`
      val edges = Set(
        (seeking, id, vec(1, 0, 1), seeking),
        // to `taking`
        (seeking, add, vec(0, 1, 1), taking),
        (taking, add, vec(0, 1, 1), taking),
        // to `ignoring`
        (seeking, id, vec(0, 0, 1), ignoring),
        (taking, id, vec(0, 0, 1), ignoring),
        (ignoring, id, vec(0, 0, 1), ignoring)
      ).map { case (p, u, v, q) => (p, curr: CurrOrDelim, u, v, q) }
      val outGraph = states.map(p => (p, id(listVar), vec(0, 0, 0))).toSet
      (edges, outGraph)
    }
    val formula = {
      val sugar = new PresburgerFormulaSugarForParikhAutomaton[String, Int]
      import sugar._
      def equalityITE(lhs: Term)(cond: Formula, `then`: Term, `else`: Term): Formula =
        (cond && (lhs === `then`)) || (!cond && (lhs === `else`))
      val Seq(b0, e0): Seq[Term] = Seq[Term](Var(Left(begin)), Var(Left(end)))
      val boundVars @ Seq(b1, b2, b3, b4, e1, e2, e3, e4): Seq[sugar.Var] = {
        val max = labels.max + 1
        Seq.tabulate[sugar.Var](8)(i => Var(Right(max + i)))
      }
      val Seq(sek, tak, inp): Seq[sugar.Var] = labels.map[sugar.Var](label => Var(Right(label)))
      val first: Formula =
        // b1 == if begin < 0 then begin + input else begin
        equalityITE(b1)(b0 < const(0), b0 + inp, b0) &&
          equalityITE(e1)(e0 < 0, e0 + inp, e0)
      val second: Formula =
        (b2 === b1) &&
          // e2 == max(b1, e1)
          equalityITE(e2)(b1 <= e1, e1, b1)
      val third: Formula = // x3 == max(x2, 0)
        equalityITE(b3)(b2 >= 0, b2, 0) &&
          equalityITE(e3)(e2 >= 0, e2, 0)
      val forth: Formula = // x4 == min(x3, input)
        equalityITE(b4)(b3 <= inp, b3, inp) &&
          equalityITE(e4)(e3 <= inp, e3, inp)
      val filter: Formula = (b4 === sek) && (e4 - b4 === tak)
      Presburger.Exists(boundVars, first && second && third && forth && filter): Formula
    }
    val internal = ParikhSST[Int, CurrOrDelim, CurrOrDelim, Int, Int, String](
      states = states.toSet,
      inSet = Set(curr),
      xs = Set(listVar),
      ls = labels.toSet,
      is = Set(begin, end),
      edges = edges,
      q0 = seeking,
      outGraph = outGraph,
      acceptFormulas = Seq(formula)
    )
    SimpleStreamingDataStringTransducer2(internal)
  }

  // DataStringTheory で定義したものから変換
  def from1[D](
      t: SimpleStreamingDataStringTransducer[D]
  ): SimpleStreamingDataStringTransducer2 { type ParikhLabel = Int } = {
    import CurrOrDelim._
    val canon = SimpleStreamingDataStringTransducer.canonicalize(t)
    def convSpec(w: canon.types.ListSpec): Cupstar[canon.ListVar, CurrOrDelim] = w.map {
      case Left(x)  => Cop1(x)
      case Right(_) => Cop2(curr)
    }.toList
    def convUpdate(u: canon.types.Update): expresso.Update[canon.ListVar, CurrOrDelim] = u._1 map {
      case (x, w) => x -> convSpec(w)
    }
    SimpleStreamingDataStringTransducer2(
      ParikhSST[canon.State, CurrOrDelim, CurrOrDelim, canon.ListVar, Int, String](
        states = canon.states,
        inSet = Set(curr, delim),
        xs = canon.listVars,
        ls = Set(),
        is = Set(),
        edges = canon.transitions map { case e =>
          val u = canon.updateOf(e)
          (canon.srcOf(e), curr, convUpdate(u), Map(), canon.dstOf(e))
        },
        q0 = canon.initialStates.head,
        outGraph = canon.outputRelation.map { case (state, spec) => (state, convSpec(spec), Map()) },
        acceptFormulas = Seq()
      )
    )
  }

  val theory1          = new DataStringTheory[Boolean]
  def reverse          = from1(SimpleStreamingDataStringTransducer.reverse)
  def identity         = from1(SimpleStreamingDataStringTransducer.identity)
  def duplicate        = from1(SimpleStreamingDataStringTransducer.duplicate)
  def reverseIdentity1 = from1(SimpleStreamingDataStringTransducer.reverseIdentity1)
  def reverseIdentity2 = from1(SimpleStreamingDataStringTransducer.reverseIdentity2)
  def reverseIdentity3 = from1(SimpleStreamingDataStringTransducer.reverseIdentity3)

  // #-区切りへのリフト

  // q0' := (0, q0), ..., (numReadStrings, q0) =: dom(F')
  // F'(..) = xin xout, xout = X.head
  // q in dom(F), (operand, q) -[#/xout := F(q)]-> (operand+1, q0)

  type SSDT = SimpleStreamingDataStringTransducer2
  val SSDT = SimpleStreamingDataStringTransducer2

  def liftDelim(
      t: SSDT,
      numReadStrings: Int,
      operand: Int
  ): SSDT = {
    type ListVar = Option[t.ListVar]
    val xin      = Option.empty[t.ListVar]
    val listVars = t.listVars.map(Option(_)) + xin
    val xout     = (listVars - xin).head
    val states =
      Set.tabulate(numReadStrings + 1)((_, t.initialState)) ++
        t.states.map((operand, _))
    val initialState = (0, t.initialState)
    val zeros        = t.parikhLabels.map(_ -> 0).toMap
    val outputRelation =
      Set(((numReadStrings, t.initialState), List(Cop1(xin), Cop1(xout), Cop2(delim: CurrOrDelim)), zeros))
    val edges = {
      type ListSpec = Cupstar[ListVar, CurrOrDelim]
      type Update   = expresso.Update[ListVar, CurrOrDelim]
      val idUpdate: Update              = expresso.Update.identity(listVars)
      val mtUpdate: Update              = expresso.Update.reset(listVars)
      def add(sym: CurrOrDelim): Update = Map(xin -> List(Cop1(xin), Cop2(sym)))
      def liftSpec(output: t.ListSpec): ListSpec = output.map {
        case Cop1(x)   => Cop1(Option(x))
        case Cop2(sym) => Cop2(sym)
      }
      def liftUpdate(update: t.Update): Update =
        for ((x, w) <- update) yield (Option(x) -> liftSpec(w))
      def setXout(output: t.ListSpec): Update = mtUpdate ++ Map(xout -> liftSpec(output))
      // i != operand, (i, q0) -[d/add, 0]-> (i, q0)
      // i != operand, (i, q0) -[#/add, 0]-> (i+1, q0)
      val notOperand = for {
        i   <- 0 to numReadStrings if i != operand
        sym <- Seq(curr, delim)
      } yield {
        val next = sym match { case `curr` => 0; case `delim` => 1 }
        ((i, t.initialState), sym, idUpdate ++ add(sym), zeros, (i + next, t.initialState))
      }
      // i == operand, (i, p)  -[d/u, v]->   (i, q) for (p, u, q) in transitions
      val lifted = t.transitions.map { case (src, _, update, vec, dst) =>
        ((operand, src), curr, liftUpdate(update) ++ add(curr), vec, (operand, dst))
      }
      // i == operand, (i, p)  -[#/u, v]->   (i+1, q0) for
      //   u == [xout := F(p)], v == F(p)
      val converted = t.outputRelation.map { case (state, output, vec) =>
        ((operand, state), delim, setXout(output) ++ add(delim), vec, (operand + 1, t.initialState))
      }
      (notOperand ++ lifted ++ converted).toSet
    }
    SSDT(
      ParikhSST(
        states = states,
        inSet = Set(curr, delim),
        xs = listVars,
        ls = t.parikhLabels,
        is = t.intParams,
        edges = edges,
        q0 = initialState,
        outGraph = outputRelation,
        acceptFormulas = t.acceptFormulae,
      )
    )
  }

  def concatDelim(numReadStrings: Int, operands: Seq[Int]): SSDT = {
    val states = (0 to numReadStrings).toSet
    val xin    = -1
    // 変数 i には operands(i) 番目の文字列を格納する
    val listVars = (xin until operands.length).toSet
    val zeros    = Map[Int, Int]()
    val edges = {
      type ListSpec = Cupstar[Int, CurrOrDelim]
      type Update   = expresso.Update[Int, CurrOrDelim]
      val idUpdate: Update = listVars.map(x => x -> List(Cop1(x))).toMap
      def add(`var`: Int, sym: CurrOrDelim): Update =
        Map(`var` -> List(Cop1(`var`), Cop2(sym)))
      // 状態 i における区切り文字による遷移では、
      // 区切り文字を xin にだけ加える。
      val delimEdges = for {
        i <- 0 until numReadStrings
      } yield {
        (i, delim, idUpdate ++ add(xin, delim), zeros, i + 1)
      }
      // 状態 i におけるデータによる遷移（ループ）では、
      // operands(j) == i となるすべての j と xin に、読んだ文字を加える。
      def inverse(i: Int): Seq[Int] = for ((x, j) <- operands.zipWithIndex if x == i) yield j
      def edgeStoring(i: Int) = {
        val storedIn = inverse(i) :+ xin
        val update   = idUpdate ++ storedIn.flatMap(add(_, curr))
        (i, curr, update, zeros, i)
      }
      (delimEdges ++ (0 until numReadStrings).map(edgeStoring)).toSet
    }
    // xin operands # を出力
    val outputRelation =
      Set(
        (
          numReadStrings,
          List.from(Cop1(xin) +: operands.indices.map(Cop1(_)) :+ Cop2(delim: CurrOrDelim)),
          zeros
        )
      )
    SSDT(
      ParikhSST(
        states = states,
        inSet = Set(curr, delim),
        xs = listVars,
        ls = Set(),
        is = Set(),
        edges = edges,
        q0 = 0,
        outGraph = outputRelation,
        acceptFormulas = Seq()
      )
    )
  }

  def projection(numReadStrings: Int, operands: Seq[Int]): SSDT = {
    val concat = concatDelim(numReadStrings, operands)
    val rel    = concat.internalSST.outGraph.head
    val spec   = rel._2
    SSDT(
      concat.internalSST.copy(
        // xin を除く
        outGraph = Set(rel.copy(_2 = spec.diff(Seq(Cop1(-1)))))
      )
    )
  }
}

private class PresSugar[X] {
  import Presburger._
  type Var     = Presburger.Var[X]
  type Term    = Presburger.Term[X]
  type Formula = Presburger.Formula[X]
  val Var                          = Presburger.Var
  implicit def const(i: Int): Term = Const(i)
  implicit class TermOps(t: Term) {
    def +(s: Term): Term      = Add(Seq(t, s))
    def -(s: Term): Term      = Sub(t, s)
    def *(i: Int): Term       = Mult(Const(i), t)
    def ===(s: Term): Formula = Eq(t, s)
    def <(s: Term): Formula   = Lt(t, s)
    def <=(s: Term): Formula  = Le(t, s)
    def >(s: Term): Formula   = Gt(t, s)
    def >=(s: Term): Formula  = Ge(t, s)
    def !==(s: Term): Formula = !(t === s)
  }
  implicit class FormulaOps(f: Formula) {
    def unary_! : Formula        = Not(f)
    def &&(g: Formula): Formula  = Conj(Seq(f, g))
    def ||(g: Formula): Formula  = Disj(Seq(f, g))
    def ==>(g: Formula): Formula = Implies(f, g)
  }
}

private class PresburgerFormulaSugarForParikhAutomaton[I, L] extends PresSugar[Either[I, L]] {
  def param(x: I): Var = Var(Left(x))
  def label(x: L): Var = Var(Right(x))

  extension (term: Presburger.Term[I]) {
    def injected: Term = term.renameVars(Left(_))
  }
}

// セマンティクスの定義
object SDSTSemantics {

  import CurrOrDelim.{curr, delim}
  type DataOrDelimSeq = Seq[Either[Int, delim.type]]
  def seq(xs: Any*): DataOrDelimSeq = xs.collect {
    case x: Int  => Left(x)
    case `delim` => Right(delim)
  }
  val :# = delim
  def transduce(
      t: SimpleStreamingDataStringTransducer2,
      args: Map[String, Int],
      xs: DataOrDelimSeq
  ): DataOrDelimSeq = {
    def vecAdd[K](u: Map[K, Int], v: Map[K, Int]): Map[K, Int] = {
      require(u.keySet == v.keySet)
      u.map { case (k, n) => k -> (n + v(k)) }
    }
    def evalSpec(
        spec: t.ListSpec,
        env: Map[t.ListVar, DataOrDelimSeq],
        data: Option[Int] = None
    ): DataOrDelimSeq = {
      // data が None なら spec は curr を含まない
      require(data.nonEmpty || spec.forall { case Cop2(`curr`) => false; case _ => true })
      spec.flatMap {
        case Cop1(x)       => env(x)
        case Cop2(`delim`) => Seq(Right(`delim`))
        case Cop2(`curr`)  => Seq(Left(data.get))
      }
    }
    def updateEnv(
        update: t.Update,
        env: Map[t.ListVar, DataOrDelimSeq],
        data: Option[Int] = None // update の curr を data で置換
    ): Map[t.ListVar, DataOrDelimSeq] =
      update.map { case (x, spec) => x -> evalSpec(spec, env, data = data) }
    val initialConfig =
      (
        t.initialState,
        Map.from(t.listVars.map(_ -> (Seq.empty: DataOrDelimSeq))),
        Map.from(t.parikhLabels.map(_ -> 0))
      )
    val finalConfigs = xs.foldLeft(Set(initialConfig)) { case (configs, dataOrDelim) =>
      configs.flatMap { case (state, listEnv, image) =>
        dataOrDelim match {
          case Left(data) =>
            for {
              case (src, `curr`, update, newImage, dst) <- t.transitions if src == state
            } yield (dst, updateEnv(update, listEnv, data = Some(data)), vecAdd(image, newImage))
          case Right(`delim`) =>
            for {
              case (src, `delim`, update, newImage, dst) <- t.transitions if src == state
            } yield (dst, updateEnv(update, listEnv), vecAdd(image, newImage))
        }
      }
    }
    val outputCandidates = for {
      (state, listEnv, image)            <- finalConfigs
      (finalState, listSpec, finalImage) <- t.outputRelation if state == finalState
    } yield (evalSpec(listSpec, listEnv), vecAdd(image, finalImage))
    val result = outputCandidates.filter { case (_, image) =>
      import expresso.math.Presburger
      val formulae = t.acceptFormulae
        // formulae には、値が与えられなかった仮引数が自由変数として残る場合がある
        .map(Presburger.Formula.substitute(_) {
          case Left(param) if args.isDefinedAt(param) => Presburger.Const(args(param))
          case Left(param)                            => Presburger.Var(Left(param))
          case Right(label)                           => Presburger.Const(image(label))
        })
      expresso.withZ3Context { ctx =>
        import com.microsoft.z3
        val solver = ctx.mkSolver()
        val z3Exprs =
          formulae.map(
            Presburger.Formula.formulaToZ3Expr(ctx, Map.empty[Either[String, t.ParikhLabel], z3.IntExpr], _)
          )
        solver.add(z3Exprs: _*)
        solver.check() == z3.Status.SATISFIABLE
      }
    }
    assert(result.size == 1, result)
    result.head._1
  }

}

private object SemanticsSpecs {

  import SDSTSemantics._

  def take(machine: SimpleStreamingDataStringTransducer2, nTake: String) = {
    for (i <- -10 to 10) {
      val expected = seq(List(1, 2, 3).take(i): _*)
      val result   = transduce(machine, Map(nTake -> i), seq(1, 2, 3))
      assert(expected == result, s"${i}: got ${result} but ${expected} expected")
    }
  }

  def drop(machine: SimpleStreamingDataStringTransducer2, nDrop: String) = {
    for (i <- -10 to 10) {
      val expected = seq(List(1, 2, 3).drop(i): _*)
      val result   = transduce(machine, Map(nDrop -> i), seq(1, 2, 3))
      assert(expected == result, s"${i}: got ${result} but ${expected} expected")
    }
  }

  def takeEven(machine: SimpleStreamingDataStringTransducer2) = {
    assert(transduce(machine, Map(), seq(1, 2, 3)) == seq(2))
    assert(transduce(machine, Map(), seq(1, 2, 3, 4)) == seq(2, 4))
    assert(transduce(machine, Map(), seq()) == seq())
  }

  def slice123(machine: SimpleStreamingDataStringTransducer2, begin: String, end: String) = {
    def transduce123(b: Int, e: Int): DataOrDelimSeq =
      transduce(machine, Map(begin -> b, end -> e), seq(1, 2, 3))
    assert(transduce123(0, 3) == seq(1, 2, 3))
    assert(transduce123(1, 2) == seq(2))
    assert(transduce123(-2, -1) == seq(2))
    assert(transduce123(1, -1) == seq(2))
    assert(transduce123(-2, 2) == seq(2))
    assert(transduce123(0, 1) == seq(1))
    assert(transduce123(-3, -2) == seq(1))
    assert(transduce123(-4, -2) == seq(1))
    assert(transduce123(2, 3) == seq(3))
    assert(transduce123(-1, 3) == seq(3))
    assert(transduce123(2, 5) == seq(3))
    assert(transduce123(1, 1) == seq())
    assert(transduce123(-1, -1) == seq())
    assert(transduce123(3, 2) == seq())
  }

  def reverse(machine: SimpleStreamingDataStringTransducer2) = {
    assert(transduce(machine, Map.empty, seq(1, 2, 3)) == seq(3, 2, 1))
    assert(transduce(machine, Map.empty, seq()) == seq())
  }

}

object DataStringTransducerExamples extends App {

  import SDSTSemantics._

  // トランスデューサのインスタンスとセマンティクスのテスト

  val reverse = SimpleStreamingDataStringTransducer2.reverse
  SemanticsSpecs.reverse(reverse)

  val slice = SimpleStreamingDataStringTransducer2.slice("b", "e")
  SemanticsSpecs.slice123(slice, "b", "e")

  import SimpleStreamingDataStringTransducer2.{concatDelim, projection, liftDelim}

  val concat = concatDelim(numReadStrings = 3, operands = Seq(1, 2))
  val projId = projection(numReadStrings = 1, operands = Seq(0))

  val i = "n"

  val (tak, drp, takeDrop) = {
    import InputCodeExamples.{defop_take, defop_drop, defprog_concatSplit}
    val repl = REPL(defop_take ++ defop_drop ++ defprog_concatSplit)
    repl.setOptions(REPL.Options(print = false))
    repl.interpretAll()
    (repl.makeSDST("take", i), repl.makeSDST("drop", i), repl.getSDST("concat-split"))
  }

  SemanticsSpecs.take(tak, i)
  SemanticsSpecs.drop(drp, i)

  def concatSplitSpec(machine: SimpleStreamingDataStringTransducer2) = {
    assert(transduce(machine, Map(i -> -2), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
    assert(transduce(machine, Map(i -> 2), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
    assert(transduce(machine, Map(i -> 5), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
  }

  concatSplitSpec(takeDrop)

  assert(transduce(concat, Map(), seq(1, :#, 2, :#, 3, :#)) == seq(1, :#, 2, :#, 3, :#, 2, 3, :#))
  assert(transduce(projId, Map(), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))

  val delimRevRev = DataStringTheory2.composeLeft(
    liftDelim(reverse, numReadStrings = 1, operand = 0),
    liftDelim(reverse, numReadStrings = 2, operand = 1),
    projection(numReadStrings = 3, operands = Seq(2))
  )
  val delimId = projection(numReadStrings = 1, operands = Seq(0))
  assert(transduce(delimRevRev, Map(), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
  println("semantics examples done")

  // 等価性判定のテスト
  import SimpleStreamingDataStringTransducer2.{
    identity,
    duplicate,
    reverseIdentity1,
    reverseIdentity2,
    reverseIdentity3,
  }
  import DataStringTheory2.{checkEquivalence, checkFunctionality, compose}
  assert(checkEquivalence(reverse, reverse))
  assert(!checkEquivalence(reverse, identity))
  assert(checkFunctionality(duplicate))
  assert(checkFunctionality(reverseIdentity1))
  assert(checkEquivalence(reverseIdentity1, reverseIdentity2))
  assert(checkEquivalence(reverseIdentity1, reverseIdentity3))
  assert(!checkEquivalence(duplicate, reverseIdentity1))
  assert(checkEquivalence(compose(reverse, reverse), identity))
  assert(checkFunctionality(tak))
  assert(checkFunctionality(drp))
  def printSize(t: SimpleStreamingDataStringTransducer2): Unit =
    println(
      s"|Q| = ${t.states.size}" ++
        ", |Δ| = ${t.transitions.size}" ++
        ", |X| = ${t.listVars.size}" ++
        ", |L| = ${t.parikhLabels.size}"
    )
  assert(checkEquivalence(delimRevRev, delimId))
  // NOTE: comp の functionality 判定は Z3 による充足可能性判定が終わらない。
  // 構成される Parikh オートマトンは 1000 状態 20000 遷移程度
  def printTime(): Unit            = println(new java.util.Date(System.currentTimeMillis()))
  def printTime(msg: String): Unit = println(s"${new java.util.Date(System.currentTimeMillis())}: $msg")
  // assert(checkFunctionality(comp))
  assert(checkEquivalence(delimId, takeDrop))
  // 特殊化された take, drop を使う例
  printTime("tak =equiv? drp")
  assert(!checkEquivalence(tak, drp))
  printTime("tak =equiv? identity")
  assert(!checkEquivalence(tak, identity))
  printTime("func? takeDrop")
  assert(checkFunctionality(takeDrop)) // この場合は 5 分程度で決定できる
  printTime("delimID =equiv? takeDrop")
  assert(checkEquivalence(delimId, takeDrop))
  println("equivalence checking examples done")
}

private class StringGenerator(private var forbidden: Set[String]) {
  private def randomString(): String = {
    import scala.util.Random
    val len = Random.between(3, 7)
    s"rand_${List.fill(len)(Random.nextPrintableChar())}"
  }
  def apply(): String = {
    val res = LazyList.from(0).map(_ => randomString()).find(!forbidden(_)).get
    forbidden += res
    res
  }
}

object DataStringTheory2 {
  private type SSDT = SimpleStreamingDataStringTransducer2
  private val SSDT = SimpleStreamingDataStringTransducer2

  /** t1 をしてから t2 をする合成 */
  def compose(t1: SSDT, t2: SSDT): SSDT =
    SSDT(t1.internalSST compose t2.internalSST)
  def composeLeft(transducers: SSDT*): SSDT =
    transducers.reduceLeft(compose)
  def checkFunctionality(t: SSDT): Boolean = checkEquivalence(t, t)
  def checkEquivalence(t1: SSDT, t2: SSDT): Boolean = {
    // require(t1.isTotal && t2.isTotal) だが、全域性は決定不能

    import Presburger.Sugar._
    import Presburger.Var

    def notEquiv = differByLength || differAtSomePosition

    def differByLength: Boolean = {
      val toParikhAutomaton = parikhAutomatonConstructionScheme(endOfOutput) _
      val (pa1, _, p1, _)   = toParikhAutomaton(t1)
      val (pa2, _, p2, _)   = toParikhAutomaton(t2)
      val p                 = pa1 intersect pa2
      p.addFormula(Var(p1) !== Var(p2)).internal.ilVectorOption.nonEmpty
    }
    def differAtSomePosition: Boolean = {
      // 結果の PA が w を受理するなら、t に w を与えるとその j 文字目が出力の "p" 文字目に現れる
      val toParikhAutomaton       = parikhAutomatonConstructionScheme(someInternalPosition) _
      val (pa1, j1, p1, isDelim1) = toParikhAutomaton(t1)
      val (pa2, j2, p2, isDelim2) = toParikhAutomaton(t2)
      val p                       = pa1 intersect pa2
      p.addFormula(
        // p1 == p2 && (isDelim1 != isDelim2 || (isDelim == 0 && j1 != j2))
        (Var(p1) === Var(p2)) &&
          ((Var(isDelim1) !== Var(isDelim2)) ||
            ((Var(isDelim1) === 0) && (Var(j1) !== Var(j2))))
      ).internal
        .ilVectorOption
        .nonEmpty
    }
    sealed trait Position
    case object someInternalPosition extends Position
    case object endOfOutput          extends Position
    // 結果を (pa, j, p, isDelim) とする。
    // pa が w を受理するとする。
    // また、t に w を入力として与えたときの出力を w' とする。
    // isDelim == 1 のとき、w' の位置 p は区切り文字である。
    // そうでないとき、w' の位置 p は w の j 文字目である。
    // ただし、出力の終端も「文字」であると考える；w' の位置 w'.length は、w の w.length 文字目である。
    def parikhAutomatonConstructionScheme(
        pPointsTo: Position
    )(t: SSDT): (SimplePA2[String], String, String, String) = {
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

      // generate parameters
      val gen           = StringGenerator(t1.intParams | t2.intParams)
      val j, p, isDelim = gen()

      enum Label                                   { case lj, lp, ld; case Wrap(x: t.ParikhLabel) }
      implicit class InjLabel(self: t.ParikhLabel) { def injected: Label = Label.Wrap(self)       }
      implicit class InjImage(self: t.ParikhImage) {
        def injected: Map[Label, Int] = self.map { case (l, v) => l.injected -> v }
      }
      import Label.{lj, lp, ld}
      // type Label = t.ParikhLabel
      // val lj                                          = t.internalSST.ls.maxOption.getOrElse(0) + 1
      // val lp                                          = lj + 1
      // val ld                                          = lj + 2
      def L(x: Label): Var[Either[String, Label]]  = Var(Right(x))
      def I(x: String): Var[Either[String, Label]] = Var(Left(x))

      val labels    = Set(lj, lp, ld)
      val intParams = Set(j, p, isDelim)
      val formula   = L(lj) === I(j) && L(lp) === I(p) && L(ld) === I(isDelim)
      val isInitial = (q: t.State, f: Guess) => t.initialStates(q) && !f.pGuessed
      lazy val finals: Set[((t.State, Guess), t.ParikhImage)] = t.outputRelation flatMap { case o =>
        val state      = t.stateOf(o)
        val outputSpec = t.outputSpecOf(o)
        val image      = t.outputImageOf(o)
        val x          = t.listVars.head
        val xs         = t.listVars - x
        val update     = xs.map(_ -> t.emptySpec) + (x -> outputSpec)
        val relativeToP = pPointsTo match {
          case `endOfOutput`          => `left`
          case `someInternalPosition` => `center`
        }
        val guess = xs.map(_ -> (unused: LRCU)) + (x -> relativeToP)
        prevGuesses(Guess.from(guess), Update.from(update)) map (f => ((state, f), image))
      }
      lazy val (states, edges) = expresso.searchStates(finals.map(_._1), Set(curr, delim)) {
        case ((r, g), sym) =>
          t.edgesTo(r).withFilter(t.inputOf(_) == sym) flatMap { e =>
            val p      = t.srcOf(e)
            val update = t.updateOf(e)
            val input  = t.inputOf(e)
            val image  = t.imageOf(e)
            def res: Iterable[(t.State, Map[Label, Int], Guess)] = prevGuesses(g, update) map { f =>
              def res = (p, image.injected ++ Map(lj -> e, lp -> c, ld -> (if (splittedAtDelim) 1 else 0)), f)
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
              res
            }
            res
          }
      }(
        c => (c._1, c._3),
        { case ((r, g), sym, (p, u, f)) => ((p, f), sym, u, (r, g)) }
      )

      def prevGuesses(guess: Guess, update: t.Update): Iterable[Guess] = {
        def candidates(x: t.ListVar): Iterable[Iterable[(t.ListVar, LRCU)]] =
          guess(x) match {
            case `left` | `right` | `unused` => Seq(update(x).listVariables.map(_ -> guess(x)))
            case `center` =>
              val w = update(x)
              (0 until w.length) map { i =>
                val (w1, z +: w2) = w.splitAt(i): @unchecked
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

      // TODO: シュガーに移動する
      def renameVars[X, Y](formulae: Seq[Presburger.Formula[X]])(
          renamer: X => Y
      ): Seq[Presburger.Formula[Y]] = formulae map (_.renameVars(renamer))
      val injectedFormulae = renameVars(t.internalSST.acceptFormulas) {
        case Left(x)  => Left(x)
        case Right(x) => Right(x.injected)
      }
      val acceptFormulae = Seq(formula) ++ injectedFormulae

      val pa = SimplePA2.from(
        SimplePA2.ExtendedSyntax[(t.State, Guess), Label, String](
          states = states,
          labels = labels ++ t.internalSST.ls.map(_.injected),
          params = Set(j, p, isDelim) ++ t.internalSST.is,
          edges = edges,
          initialStates = states.filter { case (q, f) => isInitial(q, f) },
          acceptRelation = finals.map { case (q, v) =>
            val zeroVector = Map(lj -> 0, lp -> 0)
            ((q, v.injected ++ zeroVector))
          },
          acceptFormulae = acceptFormulae
        )
      )
      (pa, j, p, isDelim)
    }

    !notEquiv
  }

}

private abstract class SimplePA2[I] { outer =>
  type State
  type Label
  val internal: ParikhAutomaton[State, CurrOrDelim, Label, I]
  def intersect(that: SimplePA2[I]): SimplePA2[I] = new SimplePA2[I] {
    type State = (outer.State, that.State)
    type Label = expresso.math.Cop[outer.Label, that.Label]
    val internal = outer.internal intersect that.internal
  }
  def addFormula(f: Presburger.Formula[I]): SimplePA2[I] = new SimplePA2[I] {
    type State = outer.State
    type Label = outer.Label
    val internal = {
      val orig                                     = outer.internal
      val fm: Presburger.Formula[Either[I, Label]] = f.renameVars(Left.apply)
      orig.copy(acceptFormulas = fm +: orig.acceptFormulas)
    }
  }
}

private object SimplePA2 {

  // 拡張したのは、今のところ初期状態が複数ありうるということだけ
  case class ExtendedSyntax[Q, L, I](
      states: Set[Q],
      labels: Set[L],
      params: Set[I],
      edges: Set[(Q, CurrOrDelim, Map[L, Int], Q)],
      initialStates: Set[Q],
      acceptRelation: Set[(Q, Map[L, Int])],
      acceptFormulae: Seq[Presburger.Formula[Either[I, L]]]
  )

  def from[Q, L, I](spec: ExtendedSyntax[Q, L, I]): SimplePA2[I] = new SimplePA2[I] {
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
        inSet = Set(CurrOrDelim.curr, CurrOrDelim.delim), // TODO: 決め打ちは良くない (?)
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

private sealed abstract class Comparator
private case object Equal extends Comparator
private enum Inequal extends Comparator {
  case Le, Lt, Ge, Gt
  def dual: Comparator = this match {
    case Le => Gt
    case Lt => Ge
    case Ge => Lt
    case Gt => Le
  }
  def isLess: Boolean = this match {
    case Le | Lt => true
    case _       => false
  }
}

private object InputFormat {

  enum ParamType { case Acc, Int, Inp }

  case object NilVal
  type NilVal = NilVal.type

  enum ListPattern {
    case Nil
    case Cons(head: String, tail: String)
  }

  case class GuardClause(name: String, comparator: Inequal, threshold: ArithExp)
  case class Guard(conjuncts: Seq[GuardClause]) {
    /// TODO: assert
    // 各 name につき conjusts は１つ
  }

  // NOTE: ArgExp の String は整数パラメタかもしれない
  type ArgExp = Append | NilVal | Increment | String
  case class Append(names: String*)
  type Increment = (Sign, String, Int)
  enum Sign {
    case Minus, Plus
    import math.Numeric.Implicits.infixNumericOps
    def apply[A: Numeric](n: A): A = if (this == Minus) -n else n
  }

  trait AExpBase {
    type exp <: Exp
    trait Exp
    protected object Exp {
      class Const(n: Int)     extends Exp
      class Var(name: String) extends Exp
      // NOTE: divisor must be Const to be linear
      class Mod(divident: exp, divisor: exp) extends Exp
      class Add(e1: exp, e2: exp)            extends Exp
      class Sub(e1: exp, e2: exp)            extends Exp
      // NOTE: args must be Const to be linear
      class Mul(e1: exp, e2: exp) extends Exp
    }
  }

  trait AExp_ToPresburger extends AExpBase {
    type exp <: ArithExp
    trait ArithExp extends super.Exp {
      def toPresburgerTerm: Presburger.Term[String]
    }
    object ArithExp {
      case class Const(n: Int) extends Exp.Const(n) with ArithExp {
        def toPresburgerTerm: Presburger.Term[String] = Presburger.Const(n)
      }
      case class Var(name: String) extends Exp.Var(name) with ArithExp {
        def toPresburgerTerm: Presburger.Term[String] = Presburger.Var(name)
      }
      case class Mod(divident: exp, divisor: exp) extends Exp.Mod(divident, divisor) with ArithExp {
        def toPresburgerTerm: Presburger.Term[String] =
          Presburger.Mod(divident.toPresburgerTerm, divisor.toPresburgerTerm)
      }
      case class Add(e1: exp, e2: exp) extends Exp.Add(e1, e2) with ArithExp {
        def toPresburgerTerm: Presburger.Term[String] =
          Presburger.Add(Seq(e1.toPresburgerTerm, e2.toPresburgerTerm))
      }
      case class Sub(e1: exp, e2: exp) extends Exp.Sub(e1, e2) with ArithExp {
        def toPresburgerTerm: Presburger.Term[String] =
          Presburger.Sub(e1.toPresburgerTerm, e2.toPresburgerTerm)
      }
      case class Mul(e1: exp, e2: exp) extends Exp.Mul(e1, e2) with ArithExp {
        def toPresburgerTerm: Presburger.Term[String] =
          Presburger.Mult(e1.toPresburgerTerm, e2.toPresburgerTerm)
      }
    }
  }
  object AExp extends AExp_ToPresburger { type exp = this.ArithExp }
  export AExp.ArithExp

  final case class FunCall(name: String, args: Seq[ArgExp])

  case class AuxFnClause(
      name: String,
      params: AuxFnParams,
      body: Seq[(Guard, Append | NilVal | String /* リスト変数 */ | FunCall)]
  )

  type AuxFnParams = (Seq[String], ListPattern)

  object NoGuard {
    def apply(x: Append | NilVal | String | FunCall): Seq[(Guard, Append | NilVal | String | FunCall)] =
      List((Guard(Nil), x))
    def unapply(
        xs: Seq[(Guard, Append | NilVal | String | FunCall)]
    ): Option[Append | NilVal | String | FunCall] =
      Option.when(xs.size == 1 && xs.head._1.conjuncts.length == 0)(xs.head._2)
  }

  sealed abstract class ProgramStatement
  final case class Assignment(lhs: String, rhs: FunCall) extends ProgramStatement

  final case class Assumption(comparator: Comparator, lhs: Assumption.Exp, rhs: Assumption.Exp)

  object Assumption extends AExpBase {
    type exp = this.Exp
    case object Length extends this.Exp
    object ArithExp {
      case class Const(n: Int)     extends Exp.Const(n)
      case class Var(name: String) extends Exp.Var(name: String)
      // NOTE: divisor must be Const to be linear
      case class Mod(divident: exp, divisor: exp) extends Exp.Mod(divident, divisor)
      case class Add(e1: exp, e2: exp)            extends Exp.Add(e1, e2)
      case class Sub(e1: exp, e2: exp)            extends Exp.Sub(e1, e2)
      // NOTE: args must be Const to be linear
      case class Mul(e1: exp, e2: exp) extends Exp.Mul(e1, e2)
    }
    export ArithExp._
  }

  /// Top-level forms

  case class DefineOperation(
      signature: (String, Seq[String]),
      definition: (String, DefinitionArgs),
      auxFnArgs: Seq[ParamType],
      auxFnClauses: Seq[AuxFnClause]
  )

  type DefinitionArgs = (Seq[NilVal | ArithExp], String /* リスト変数の名前 */ )

  case class DefineProgram(
      name: String,
      intParams: Seq[String],
      inputList: String,
      intermidiateLists: Seq[String],
      outputList: String,
      body: Seq[ProgramStatement]
  ) {
    private val listNames        = Seq(inputList) ++ intermidiateLists ++ Seq(outputList)
    private val nthListName      = listNames.zipWithIndex.toMap
    private val definedListNames = body map { case Assignment(name, _) => name }
    // 中間生成リストや出力リストとして指定された通りの順に、その値が定義される
    require(((intermidiateLists ++ Seq(outputList)) zip definedListNames).forall(_ == _))
    def makeSDST(
        env: String => Seq[String] => SimpleStreamingDataStringTransducer2
    ): SimpleStreamingDataStringTransducer2 = {
      val delimitedStringTransducers: Seq[SimpleStreamingDataStringTransducer2] =
        body.zipWithIndex map {
          case (Assignment(definedVar, FunCall(funName, funArgs: Seq[String])), ithStatement) =>
            val numReadStrings = 1 /* inputList */ + ithStatement
            if (funName == "++") // TODO: 特別扱いされるべき関数が他にないか考える
              SimpleStreamingDataStringTransducer2
                .concatDelim(numReadStrings = numReadStrings, operands = funArgs map nthListName)
            else {
              val intArgs: Seq[String] = funArgs.init
              val listInput: String    = funArgs.last
              SimpleStreamingDataStringTransducer2.liftDelim(
                env(funName)(intArgs),
                numReadStrings = numReadStrings,
                operand = nthListName(listInput)
              )
            }
        }
      // TODO: funArgs には length 関数を含む算術式も使いたい
      val projection =
        SimpleStreamingDataStringTransducer2
          .projection(numReadStrings = listNames.length, operands = Seq(nthListName(outputList)))
      val transducers = delimitedStringTransducers ++ Seq(projection)
      DataStringTheory2.composeLeft(transducers: _*)
    }
  }

  case class DefineComposition(name: String, funcNames: Seq[String])

  case class CheckEquiv(name1: String, name2: String, assumptions: Seq[Assumption])

  extension (description: InputFormat.DefineOperation) {
    def toSDST(paramNames: String*) =
      GuardedSDST_withShortcuts.fromInputFormat(description)(paramNames).shortcutsEliminatedByEmulation.toSDST
  }

  type Command = DefineOperation | DefineProgram | CheckEquiv

}

private object InputCodeExamples extends App {

  val defop_take = """
;; defop -- define operator
;; 引数は整数が先で、最後は必ず入力リスト。
;;      シグネチャ   定義
(defop (take n l) (rec nil n l)
  ;; 補助関数の引数の種類のリスト
  ;; acc   - 蓄積 (accumulator) であり、SDST のリスト変数に対応する
  ;; param - 整数パラメタ
  ;; input - 入力リスト
  :aux-args acc param input
  :where ; 補助関数の定義たち
  ;; 各節の car は関数名、引数名と、入力リストについてのパターンマッチを持つ。
  ((rec acc n nil) acc)    ; 入力リストが空
  ((rec acc n (cons x xs)) ; 入力リストが非空
   (cond ; 整数引数に関するガードによる場合分け
    ((> n 0)  (rec (++ acc (list x)) (- n 1) xs))
    ((<= n 0) acc))))
"""

  val defop_drop = """
(defop (drop n l) (rec nil n l)
  :aux-args acc param input
  :where
  ((rec acc n nil) acc)
  ((rec acc n (cons x xs))
   (cond
     ((> n 0) (rec acc (- n 1) xs))
     ((<= n 0) (++ (list x) xs)))))
"""

  val defop_identity = """
(defop (identity l) (r nil l) :aux-args acc input
  :where
  ((r acc nil) acc)
  ((r acc (cons x xs)) (r (++ acc (list x)) xs)))
"""

  val defprog_concatSplit = """
;; 直線プログラムの定義
(defprog concat-split
  :param n   ; 整数引数に名前をつける
  :input inp ; 入力リストに名前をつける
  :inter x y ; 中間生成物に名前をつける
  :output z   ; 出力リストに名前をつける
  :body ; 定義本体
  (:= x (take n inp))
  (:= y (drop n inp))
  (:= z (++ x y)))
"""

  val defprog_identity = """
(defprog identity :input x :output y
  :body (:= y (identity x)))
"""

  val equiv_concatSplit_identity = """
(equiv?! concat-split identity)
"""

  val script_01 =
    defop_take ++ defop_drop ++ defop_identity ++ defprog_concatSplit ++ defprog_identity ++ equiv_concatSplit_identity

  val script_02 = """
;; 偶数番目だけを取る
(defop (take-even l) (te0 nil l)
  :aux-args acc input
  :where
  ((te0 acc nil)         acc)
  ((te0 acc (cons x xs)) (te1 acc xs))
  ((te1 acc nil)         acc)
  ((te1 acc (cons x xs)) (te0 (++ acc (list x)) xs)))

(defop (reverse l) (rec nil l)
  :aux-args acc input
  :where
  ((rec acc nil)         acc)
  ((rec acc (cons x xs)) (rec (++ (list x) acc) xs)))

(defprog te-rev :input x :inter y :output z
  :body
  (:= y (reverse x))
  (:= z (take-even y)))

(defprog rev-te :input x :inter y :output z
  :body
  (:= y (take-even x))
  (:= z (reverse y)))

(equiv?! te-rev rev-te) ; not equivalent

;; 奇数長の入力リストに対しては等価
(equiv?! te-rev rev-te :assumption (= (mod length 2) 1)) ; equivalent
"""
}

private object Reader {
  def apply(string: String): Reader = new Reader(new java.io.StringReader(string))

  import InputFormat._
  import smtlib.trees.Terms.{SExpr, SList, SSymbol, SKeyword, SNumeral}

  trait SListParser[+A] extends Function1[Seq[SExpr], Seq[(A, Seq[SExpr])]]
  private val ParserSeqImpl = LazyList

  extension [A](self: SListParser[A]) {

    def flatMap[B](that: A => SListParser[B]): SListParser[B] =
      x => self(x) flatMap { case (a, rest) => that(a)(rest) }

    def map[B](that: A => B): SListParser[B] = flatMap(x => unit(that(x)))

    def |[B](that: SListParser[B]): SListParser[A | B]  = x => self(x) ++ that(x)
    def *[B](that: SListParser[B]): SListParser[(A, B)] = for (x <- self; y <- that) yield (x, y)

    def >>[B](that: SListParser[B]): SListParser[B] = flatMap(_ => that)

    // 読み残しがないものを返す
    def parse(x: Seq[SExpr]): Option[A] = self(x) find { case (y, rest) => rest.isEmpty } map (_._1)

  }

  val zero: SListParser[Nothing] = xs => ParserSeqImpl()

  def unit[A](x: A): SListParser[A] = xs => ParserSeqImpl((x, xs))

  val head: SListParser[SExpr] =
    xs => if (xs.isEmpty) ParserSeqImpl.empty else ParserSeqImpl((xs.head, xs.tail))

  def sat(cond: SExpr => Boolean): SListParser[SExpr] = head flatMap (x => if (cond(x)) unit(x) else zero)

  def lift[A](f: PartialFunction[SExpr, A]): SListParser[A] = for {
    x <- sat(f.isDefinedAt(_))
  } yield f(x)

  def list[A](contents: SListParser[A]): SListParser[A] = xs => {
    val unwrap = lift { case SList(xs) => xs }
    for {
      (sexprs, rest) <- unwrap(xs)
      x              <- contents.parse(sexprs)
    } yield (x, rest)
  }

  def constSymbol(name: String): SListParser[Unit] = lift { case SSymbol(`name`) => () }

  val symbol: SListParser[String] = lift { case SSymbol(name) => name }

  def unionMap[A, B](spec: A*)(f: A => SListParser[B]): SListParser[B] = spec map f reduce (_ | _)

  def reserved[A](mapping: (String, A)*): SListParser[A] =
    unionMap(mapping: _*) { case (name, value) => constSymbol(name) >> unit(value) }

  val nil: SListParser[NilVal] = reserved("nil" -> NilVal)

  val numeral: SListParser[BigInt] = lift { case SNumeral(x) => x }

  val int: SListParser[Int] = numeral map { value =>
    require(value.isValidInt)
    value.toInt
  }

  def funcall[A](funName: String)(arguments: SListParser[A]): SListParser[A] =
    list(constSymbol(funName) >> arguments)

  val arith: SListParser[ArithExp] = new SListParser[ArithExp] {
    val variable = symbol map (name => ArithExp.Var(name))
    val const    = int map ArithExp.Const.apply
    def bop(xs: Seq[SExpr]) = {
      val p = unionMap(
        "+"   -> ArithExp.Add.apply,
        "-"   -> ArithExp.Sub.apply,
        "*"   -> ArithExp.Mul.apply,
        "mod" -> ArithExp.Mod.apply,
      ) { case (op, construct) => funcall(op)((this * this) map (construct(_, _))) }
      p(xs)
    }
    def apply(xs: Seq[SExpr]) = variable(xs) ++ const(xs) ++ bop(xs)
  }

  def many1[A](p: SListParser[A]): SListParser[Seq[A]] = for {
    x  <- p
    xs <- many(p)
  } yield (x +: xs)

  def many[A](p: SListParser[A]): SListParser[Seq[A]] = many1(p) | unit(Nil)

  def keyword(name: String): SListParser[Unit] = lift { case SKeyword(`name`) => () }

  def keywordArgs[A](keywordName: String)(p: SListParser[A]): SListParser[A] = keyword(keywordName) >> p

  val auxFnType: SListParser[ParamType] =
    reserved("acc" -> ParamType.Acc, "param" -> ParamType.Int, "input" -> ParamType.Inp)

  def flatMany[A](p: SListParser[Seq[A]]): SListParser[Seq[A]] = many(p) map (_.flatten)

  // TODO: "++" の引数の nil も空列とみなす場合、ここも修正する
  // TODO: パーサのレベルで (++ acc (list x)) を Append(acc, x) にするのは少し変
  val append: SListParser[Append] = {
    val listCall   = funcall("list")(many(symbol))
    val manySymbol = many(symbol)
    val operands = many(listCall | symbol) map { seq =>
      seq.foldRight(List.empty[String]) {
        case (x: String, acc)       => x :: acc
        case (xs: Seq[String], acc) => xs ++: acc
      }
    }
    funcall("++")(operands map Append.apply)
  }

  // type ArgExp = Append | NilVal | Increment | String
  val auxFunCall: SListParser[FunCall] = {
    val increment: SListParser[Increment] = {
      val plus  = funcall("+")((symbol * int) map { case (name, value) => (Sign.Plus, name, value) })
      val minus = funcall("-")((symbol * int) map { case (name, value) => (Sign.Minus, name, value) })
      plus | minus
    }
    val arg = append | nil | symbol | increment
    list(for {
      name <- symbol
      args <- many(arg)
    } yield FunCall(name, args))
  }

  type AuxFnBody = Append | NilVal | String | FunCall // TODO: InputFormat に移動
  val pattern: SListParser[(String, AuxFnParams)] = list {
    val listPattern =
      reserved("nil" -> ListPattern.Nil) | funcall("cons")((symbol * symbol) map ListPattern.Cons.apply)
    for {
      name      <- symbol
      auxParams <- many(symbol)
      lpat      <- listPattern
    } yield (name, (auxParams, lpat))
  }
  // NOTE: "++" を特別扱いしたいので append を優先する
  val auxFnBody: SListParser[AuxFnBody]             = nil | symbol | append | auxFunCall
  val noGuard: SListParser[Seq[(Guard, AuxFnBody)]] = auxFnBody map NoGuard.apply
  val inequal: SListParser[Inequal] =
    reserved(">" -> Inequal.Gt, ">=" -> Inequal.Ge, "<" -> Inequal.Lt, "<=" -> Inequal.Le)
  val guard: SListParser[Guard] = {
    val clause = list(for {
      ineq      <- inequal
      name      <- symbol
      threshold <- arith
    } yield GuardClause(name, ineq, threshold))
    val and = funcall("and")(many(clause))
    (and | (clause map (x => Seq(x)))) map Guard.apply
  }
  val condCase: SListParser[(Guard, AuxFnBody)]       = list(guard * auxFnBody)
  val caseSplit: SListParser[Seq[(Guard, AuxFnBody)]] = funcall("cond")(many(condCase))
  val auxFnClause: SListParser[AuxFnClause] = {
    // for-式で書くと、「`foreach` が無い」と怒られる
    list {
      pattern flatMap { case (name, params) =>
        (noGuard | caseSplit) map { body =>
          AuxFnClause(name, params, body)
        }
      }
    }
  }

  val assignment: SListParser[Assignment] = list(for {
    _   <- keyword("=")
    lhs <- symbol
    rhs <- auxFunCall
  } yield Assignment(lhs, rhs))

  // TODO: キーワード引数を渡す順番は交換可能であるようにする

  val signature = list {
    for {
      name   <- symbol
      params <- many(symbol)
    } yield (name, params)
  }

  val definition = list {
    for {
      name      <- symbol
      auxArgs   <- many(nil | arith)
      inputList <- symbol
    } yield (name, (auxArgs, inputList))
  }

  val defop: SListParser[Command] = list {
    for {
      _            <- constSymbol("defop")
      sig          <- signature
      dfn          <- definition
      auxFnArgs    <- keywordArgs("aux-args")(many(auxFnType))
      auxFnClauses <- keywordArgs("where")(many(auxFnClause))
    } yield DefineOperation(sig, dfn, auxFnArgs, auxFnClauses)
  }

  val defprog: SListParser[Command] = list {
    for {
      _      <- constSymbol("defprog")
      name   <- symbol
      params <- optionSeq(keywordArgs("param")(many(symbol)))
      input  <- keywordArgs("input")(symbol)
      inter  <- optionSeq(keywordArgs("inter")(many(symbol)))
      output <- keywordArgs("output")(symbol)
      body   <- keywordArgs("body")(many(assignment))
    } yield DefineProgram(name, params, input, inter, output, body)
  }

  def optionSeq[A](p: SListParser[Seq[A]]): SListParser[Seq[A]] = p | unit(Nil)

  val comparator: SListParser[Comparator] = inequal | reserved("=" -> Equal)

  val assumptionExp: SListParser[Assumption.Exp] = new SListParser[Assumption.Exp] {
    val length   = constSymbol("length") >> unit(Assumption.Length)
    val variable = symbol map (name => Assumption.Var(name))
    val const    = int map Assumption.Const.apply
    def bop(xs: Seq[SExpr]) = {
      val p = unionMap(
        "+"   -> Assumption.Add.apply,
        "-"   -> Assumption.Sub.apply,
        "*"   -> Assumption.Mul.apply,
        "mod" -> Assumption.Mod.apply,
      ) { case (op, construct) => funcall(op)((this * this) map (construct(_, _))) }
      p(xs)
    }
    def apply(xs: Seq[SExpr]) = length(xs) ++ variable(xs) ++ const(xs) ++ bop(xs)
  }
  val assumptions: SListParser[Seq[Assumption]] = keywordArgs("assumption")(many(list(for {
    comp <- comparator
    lhs  <- assumptionExp
    rhs  <- assumptionExp
  } yield Assumption(comp, lhs, rhs))))

  val equiv: SListParser[Command] = list {
    for {
      _           <- constSymbol("equiv?!")
      name1       <- symbol
      name2       <- symbol
      assumptions <- optionSeq(assumptions)
    } yield CheckEquiv(name1, name2, assumptions)
  }

  def read[A](p: SListParser[A])(sexpr: SExpr): Option[A] = p.parse(ParserSeqImpl(sexpr))

  val readCommand: SExpr => Option[Command] = read(defop | defprog | equiv)

}

private class Reader(private val reader: java.io.Reader) {

  import InputFormat.Command
  import smtlib.parser.ParserCommon
  import smtlib.lexer.{Lexer, Tokens}
  import reflect.Selectable.reflectiveSelectable

  private class SExprParser(val lexer: Lexer) extends ParserCommon {
    def current = peekToken
  }

  private val parser = new SExprParser(new Lexer(reader))

  // private def readSExpr = parser.parseSExpr
  private def readSExpr = Option.when(parser.current != null)(parser.parseSExpr)

  // 失敗したら例外を投げる
  def apply(): Option[Command] = readSExpr map (x => Reader.readCommand(x).get)

}

private object ReaderExamples extends App {

  export Reader._

  import InputCodeExamples._
  import smtlib.parser.ParserCommon
  import smtlib.lexer.Lexer

  def parseSExprInString(w: String) = {
    val reader = new java.io.StringReader(w)
    val parser = new ParserCommon { val lexer = new Lexer(reader) }
    parser.parseSExpr
  }

  def readInString[A](p: SListParser[A])(code: String): Option[A] = read(p)(parseSExprInString(code))

  def readAndPrint[A](p: SListParser[A])(code: String): Unit = {
    println(";;; read")
    println(code)
    println(";;; result")
    println(readInString(p)(code))
  }

  readAndPrint(defop)(code = defop_take)
  readAndPrint(defop)(code = defop_drop)
  readAndPrint(defop)(code = defop_identity)
  readAndPrint(defprog)(defprog_concatSplit)
  readAndPrint(equiv)(equiv_concatSplit_identity)

}

private class Evaluator {

  import InputFormat._

  private val sdstScheme       = MMap.empty[String, Seq[String] => SimpleStreamingDataStringTransducer2]
  private[machine] val sdstEnv = MMap.empty[String, SimpleStreamingDataStringTransducer2]

  def apply(command: Command): Any = command match {
    case comm: DefineOperation =>
      val name = comm.signature._1
      sdstScheme.addOne(name -> (comm.toSDST _))
      s"defop $name"
    case comm: DefineProgram =>
      sdstEnv.addOne(comm.name -> comm.makeSDST(sdstScheme))
      s"defprog ${comm.name}"
    case comm: CheckEquiv => checkEquiv(sdstEnv(comm.name1), sdstEnv(comm.name2), comm.assumptions)
  }

  private val theory = DataStringTheory2

  def checkEquiv(
      t1: SimpleStreamingDataStringTransducer2,
      t2: SimpleStreamingDataStringTransducer2,
      assumptions: Seq[Assumption]
  ) = {
    require(assumptions.isEmpty, assumptions) // TODO: とりあえず動かすための仮定
    if (theory.checkEquivalence(t1, t2)) println("equivalent")
    else println("not equivalent")
  }

  // for tests and debugging

  def makeSDST(name: String, paramNames: String*): SimpleStreamingDataStringTransducer2 =
    sdstScheme(name)(paramNames)

  def getSDST(name: String): SimpleStreamingDataStringTransducer2 = sdstEnv(name)

}

private class REPL(reader: java.io.Reader) {

  private val read = new Reader(reader)
  private val eval = new Evaluator

  def interpretOne(): Option[Unit] = read() map eval.apply map this.println

  def interpretAll(): Unit = interpretOne() foreach (_ => interpretAll())

  // option handling

  private var options = REPL.Options()

  def println(x: Any): Unit = if (options.print) Predef.println(x) else ()

  def setOptions(opts: REPL.Options = REPL.Options()) = options = opts

  // for tests and debugging

  export eval.{makeSDST, getSDST}

}

private object REPL {
  def apply(w: String): REPL               = new REPL(new java.io.StringReader(w))
  def apply(file: java.io.File): REPL      = new REPL(new java.io.FileReader(file))
  def apply(is: java.io.InputStream): REPL = new REPL(new java.io.InputStreamReader(is))

  case class Options(print: Boolean = true)
}

import com.monovore.decline

object Eqlisp
    extends decline.CommandApp(
      name = "eqlisp",
      header = "decide equivalence of list programs",
      main = {
        import decline._
        val inputStream: Opts[java.io.InputStream] =
          Opts.apply(System.in)
        inputStream map (is => REPL(is).interpretAll())
      }
    )

private object REPLExamples extends App {
  import InputCodeExamples._
  REPL(script_01).interpretAll()
  REPL(script_02).interpretAll()
}

private object InputFormatExamples extends App {
  import InputFormat._
  // ($n: Int) -> [a] -> [a] -- $n は名前が入る穴
  // "String => Simple SDST"
  val take = DefineOperation(
    signature = ("take", List("n", "l")),                          // (take n l)
    definition = ("t", (List(NilVal, ArithExp.Var("n")), "l")),    // (t nil n l)
    auxFnArgs = List(ParamType.Acc, ParamType.Int, ParamType.Inp), // :aux-args acc param input
    auxFnClauses = List(
      // ((t acc n nil) acc)
      AuxFnClause(
        name = "t",
        params = (List("acc", "n"), ListPattern.Nil),
        body = List((Guard(Nil), Append("acc")))
      ),
      AuxFnClause(
        name = "t",
        params = (List("acc", "n"), ListPattern.Cons("x", "xs")),
        body = List(
          ( // ((> n 0) (t (++ acc (x)) (- n 1) xs))
            Guard(List(GuardClause("n", Inequal.Gt, ArithExp.Const(0)))),
            FunCall("t", List(Append("acc", "x"), (Sign.Minus, "n", 1), "xs"))
          ),
          // ((<= n 0) acc)
          (Guard(List(GuardClause("n", Inequal.Le, ArithExp.Const(0)))), "acc")
        )
      )
    )
  )

  val drop = DefineOperation(
    signature = ("drop", List("n", "l")),                          // (drop n l)
    definition = ("rec", (List(NilVal, ArithExp.Var("n")), "l")),  // (rec nil n l)
    auxFnArgs = List(ParamType.Acc, ParamType.Int, ParamType.Inp), // :aux-args acc param input
    auxFnClauses = List(
      // ((rec acc n nil) acc)
      AuxFnClause(
        name = "rec",
        params = (List("acc", "n"), ListPattern.Nil),
        body = List((Guard(Nil), Append("acc")))
      ),
      AuxFnClause(
        name = "rec",
        params = (List("acc", "n"), ListPattern.Cons("x", "xs")),
        body = List(
          ( // ((> n 0) (rec acc (- n 1) xs))
            Guard(List(GuardClause("n", Inequal.Gt, ArithExp.Const(0)))),
            FunCall("rec", List("acc", (Sign.Minus, "n", 1), "xs"))
          ),
          // ((<= n 0) (++ (list x) xs))
          (Guard(List(GuardClause("n", Inequal.Le, ArithExp.Const(0)))), Append("x", "xs"))
        )
      )
    )
  )

  SemanticsSpecs.take(take.toSDST("c"), "c")

  SemanticsSpecs.drop(drop.toSDST("c"), "c")

  // [a] -> [a]
  // "Unit => Simple SDST"
  val takeEven = DefineOperation(
    signature = ("take-even", List("l")),
    definition = ("te0", (List(NilVal), "l")),
    auxFnArgs = List(ParamType.Acc, ParamType.Inp),
    auxFnClauses = List(
      AuxFnClause("te0", (List("acc"), ListPattern.Nil), NoGuard("acc")),
      AuxFnClause(
        "te0",
        (List("acc"), ListPattern.Cons("x", "xs")),
        NoGuard(FunCall("te1", List("acc", "xs")))
      ),
      AuxFnClause("te1", (List("acc"), ListPattern.Nil), NoGuard("acc")),
      AuxFnClause(
        "te1",
        (List("acc"), ListPattern.Cons("x", "xs")),
        NoGuard(FunCall("te0", List(Append("acc", "x"), "xs")))
      ),
    )
  )

  SemanticsSpecs.takeEven(takeEven.toSDST())

  val eval = new Evaluator
  eval(take)
  eval(drop)

  // (n: String) -> [a] -> [a]
  // "Simple Parikh SDST"
  val concatSplit = DefineProgram(
    // (defprog concat-split
    name = "concat-split",
    intParams = List("n"),                               // :param n
    inputList = "inp",                                   // :input inp
    intermidiateLists = List("x", "y"),                  // :inter x y
    outputList = "z",                                    // :ouput z
    body = List(                                         // :body
      Assignment("x", FunCall("take", Seq("n", "inp"))), // (:= x (take n inp))
      Assignment("y", FunCall("drop", Seq("n", "inp"))), // (:= y (drop n inp))
      Assignment("z", FunCall("++", Seq("x", "y"))),     // (:= z (++ x y))
    )
  )

  eval(concatSplit)

  val id = DefineProgram(
    name = "identity",
    intParams = Nil,
    inputList = "x",
    intermidiateLists = Nil,
    outputList = "y",
    body = List(Assignment("y", FunCall("++", Seq("x"))))
  )

  eval(id)

  val checkEquiv_concatSplit_identity = CheckEquiv(
    name1 = "concat-split",
    name2 = "identity",
    assumptions = Nil
  )

  eval(checkEquiv_concatSplit_identity)

  val checkEquiv_revTO_TOrev = CheckEquiv(
    name1 = "rev-to",
    name2 = "to-rev",
    assumptions =
      List(Assumption(Equal, Assumption.Mod(Assumption.Length, Assumption.Const(2)), Assumption.Const(1)))
  )

}

private case object restInp

// 間違えて GuardedSDST として使うことがない
private abstract class GuardedSDST_withShortcuts {
  import CurrOrDelim.{curr as currPtr}
  val sdst: GuardedSDST
  export sdst._
  type ListSpec = Cupstar[ListVar, currPtr.type | restInp.type]
  type Shortcut = (State, Guard, ListSpec)
  val shortcuts: Set[Shortcut]

  override def toString: String =
    s"states=${states}" ++
      s"initialState=${initialState}" ++
      s"listVars=${listVars}" ++
      s"labels=${labels}" ++
      s"params=${params}" ++
      s"initialParikhImage=${initialParikhImage}" ++
      s"transitions=${transitions}" ++
      s"outputFunction=${outputFunction}" ++
      s"shortcuts=${shortcuts}"

  def shortcutsEliminatedByEmulation: GuardedSDST = {
    // If (p, phi, w) \in shortcuts, then
    // introduce c_1, ..., c_m for curr,
    // r_1, ..., r_n for rest, and new state q'.

    // fresh list var for i-th curr or rest
    enum NewListVar { case Wrap(x: ListVar); case Curr(i: Int); case Rest(i: Int) }
    // fresh state for d-th shortcut
    enum NewState { case Wrap(q: State); case New(d: Int) }

    implicit class InjState(q: State)     { def injected = NewState.Wrap(q)   }
    implicit class InjListVar(x: ListVar) { def injected = NewListVar.Wrap(x) }

    val orderedShortcuts = shortcuts.toSeq

    val maxCurr            = orderedShortcuts.map(s => s._3.count(_ == Cop2(currPtr))).maxOption.getOrElse(0)
    val maxRest            = orderedShortcuts.map(s => s._3.count(_ == Cop2(restInp))).maxOption.getOrElse(0)
    val currVars           = (0 until maxCurr) map (i => NewListVar.Curr(i))
    val restVars           = (0 until maxRest) map (i => NewListVar.Rest(i))
    val additionalListVars = currVars ++ restVars

    val additionalStates = (0 until orderedShortcuts.length) map (NewState.New(_))

    val zeros = ParikhImage.zeros(labels)

    val newListVars = listVars.map(_.injected) ++ additionalListVars
    val newStates   = states.map(_.injected) ++ additionalStates

    val identityUpdate                                  = expresso.Update.identity(newListVars)
    def cop1[A, B](x: A): expresso.math.Cop[A, B]       = expresso.math.Cop1(x)
    def cop2[A](x: A): expresso.math.Cop[NewListVar, A] = expresso.math.Cop2(x)
    def overrideVariables[A](vars: Iterable[NewListVar], string: Seq[A]): expresso.Update[NewListVar, A] =
      Map.from(vars.map(x => x -> string.map(cop2).toList))
    def appendToVariables[A](vars: Iterable[NewListVar], string: Seq[A]): expresso.Update[NewListVar, A] =
      Map.from(vars.map(x => x -> (Seq(cop1(x)) ++ string.map(cop2)).toList))
    val rememberCurr = identityUpdate ++ overrideVariables[currPtr.type](currVars, Seq(currPtr))
    val appendToRest = identityUpdate ++ appendToVariables[currPtr.type](restVars, Seq(currPtr))

    val additionalTransitions =
      MSet.empty[(NewState, Guard, expresso.Update[NewListVar, currPtr.type], ParikhImage, NewState)]
    val additionalOutput = MMap.empty[NewState, Seq[NewListVar]]
    for (((state, guard, spec), d) <- orderedShortcuts.zipWithIndex) {
      val substitute: Seq[Cop[ListVar, currPtr.type | restInp.type]] => Seq[NewListVar] = { xs =>
        val cntCurr, cntRest = Counter(-1)
        xs map {
          case Cop2(x) if x == currPtr => NewListVar.Curr(cntCurr.add1)
          case Cop2(x) if x == restInp => NewListVar.Rest(cntRest.add1)
          case Cop1(x)                 => x.injected
        }
      }
      val loop = NewState.New(d)
      additionalTransitions.add((state.injected, guard, rememberCurr, zeros, loop))
      additionalTransitions.add((loop, guard, appendToRest, zeros, loop))
      additionalOutput.addOne((loop, substitute(spec)))
    }

    implicit class InjCupstar(w: expresso.Cupstar[ListVar, currPtr.type]) {
      def injected = w map { _.map1(_.injected) }
    }
    implicit class InjUpdate(u: Update) {
      def injected = identityUpdate ++ u.map { case (x, w) => x.injected -> w.injected }
    }
    implicit class InjEdge(e: Edge) {
      def injected = (srcOf(e).injected, guardOf(e), updateOf(e).injected, imageOf(e), dstOf(e).injected)
    }
    implicit class InjSpec(w: Seq[ListVar])         { def injected = w map (_.injected)             }
    implicit class InjOut(o: (State, Seq[ListVar])) { def injected = o._1.injected -> o._2.injected }
    val injectedTransitions    = transitions map (_.injected)
    val injectedOutputFunction = outputFunction map (_.injected)

    val newTransitions    = injectedTransitions ++ additionalTransitions
    val newOutputFunction = injectedOutputFunction ++ additionalOutput

    val types = new GuardedTypes[NewState, NewListVar, ParikhLabel]

    GuardedSDST(
      types,
      newStates,
      initialState.injected,
      newListVars,
      labels,
      params,
      initialParikhImage,
      newTransitions,
      newOutputFunction
    )
  }
}

private class GuardedTypes[Q, X, L] {

  import CurrOrDelim.{curr as currPtr}

  type State       = Q
  type ListVar     = X
  type ParikhLabel = L

  type Param = String

  type Update      = expresso.Update[ListVar, currPtr.type]
  type ParikhImage = Map[ParikhLabel, Int] // 負でも良い
  type ParamTerm   = Presburger.Term[Param]
  type Guard       = Map[ParikhLabel, (Inequal, ParamTerm)]
  type Transition  = (State, Guard, Update, ParikhImage, State)
  type Shortcut    = (State, Guard, Cupstar[ListVar, currPtr.type | restInp.type])

  type MachineWithoutShortcuts = GuardedSDST { type State = Q; type ListVar = X; type ParikhLabel = L }
  type MachineWithShortcuts = GuardedSDST_withShortcuts {
    type State = Q; type ListVar = X; type ParikhLabel = L
  }

}

private object GuardedSDST_withShortcuts {

  def fromInputFormat(description: InputFormat.DefineOperation): Seq[String] => GuardedSDST_withShortcuts =
    (paramNames: Seq[String]) => {
      import InputFormat._
      import CurrOrDelim.{curr => currPtr}

      val types = new GuardedTypes[String, Int, Int]

      val states                           = description.auxFnClauses.map(_.name).toSet
      val (initialState, definitionParams) = description.definition
      val (defNonInput, defInputList)      = definitionParams
      val nListVars                        = defNonInput.count(_ == NilVal)
      val nLabels                          = defNonInput.count(_ != NilVal)
      val listVars                         = Set.from(0 until nListVars)
      val labels                           = Set.from(0 until nLabels)
      val params                           = Set.from(paramNames)
      val signatureParams                  = description.signature._2.init
      require(paramNames.length == signatureParams.length)
      val paramName = Map.from(signatureParams zip paramNames)
      def translateArithExp[A >: ArithExp]: PartialFunction[A, Presburger.Term[String]] = {
        case x: ArithExp => x.toPresburgerTerm.renameVars(paramName)
      }
      val defArithExps       = defNonInput collect translateArithExp
      val initialParikhImage = Map.from(defArithExps.zipWithIndex.map(_.swap))
      val (nilClauses, consClauses) = description.auxFnClauses partition {
        case AuxFnClause(_, (_, ListPattern.Nil), _)        => true
        case AuxFnClause(_, (_, ListPattern.Cons(_, _)), _) => false
      }
      type AccOrInt = ParamType.Acc.type | ParamType.Int.type
      def zipParamsWithTypes(params: Seq[String]): Seq[(String, AccOrInt)] = {
        val types = description.auxFnArgs.collect[AccOrInt] { case x: AccOrInt => x }
        params zip types
      }
      def partitionParamsByTypes(params: Seq[String]): (Seq[String] /* Aux */, Seq[String] /* Int */ ) = {
        val map = zipParamsWithTypes(params).toMap[String, AccOrInt]
        params partition (name =>
          map(name) match {
            case ParamType.Acc => true
            case ParamType.Int => false
          }
        )
      }
      def paramTranslation(params: Seq[String]): (Map[String, Int], Map[String, Int]) = {
        val (auxParams, intParams) = partitionParamsByTypes(params)
        val trAux                  = auxParams.zipWithIndex.toMap
        val trInt                  = intParams.zipWithIndex.toMap
        (trAux, trInt)
      }
      val outputFunction = nilClauses.map { case AuxFnClause(name, (params, _), body) =>
        val (auxParams, intParams)                      = partitionParamsByTypes(params)
        val listVar                                     = auxParams.zipWithIndex.toMap
        val NoGuard(output: (Append | NilVal | String)) = body: @unchecked
        val spec = output match {
          case Append(names: _*) => names.map(listVar)
          case NilVal            => Nil
          case x: String         => List(listVar(x))
        }
        name -> spec
      }.toMap
      val expandedConsClauses = for {
        AuxFnClause(name, params, body) <- consClauses
        (guard, next)                   <- body
      } yield (name, params, guard, next)
      val (transClauses, shortClauses) = expandedConsClauses partitionMap { case cls @ (_, _, _, next) =>
        next match {
          case x: FunCall                    => Left(cls.copy(_4 = x))
          case x: (Append | NilVal | String) => Right(cls.copy(_4 = x))
        }
      }
      def translateGuard(intParams: Map[String, Int], guard: InputFormat.Guard): types.Guard =
        Map.from(guard.conjuncts map { case GuardClause(name, comparator, threshold) =>
          intParams(name) -> (comparator, translateArithExp(threshold))
        })
      def translateListParam[A](special: PartialFunction[String, A], auxParams: String => Int)(
          x: String
      ): Cop[Int, A] = x match {
        case _ if special.isDefinedAt(x) => Cop2(special(x))
        case _                           => Cop1(auxParams(x))
      }
      // TODO: types
      def translateOutput[A](
          special: PartialFunction[String, A],
          auxParams: String => Int,
          output: Append | NilVal | String
      ): Cupstar[Int, A] = {
        val trVar = translateListParam(special, auxParams)
        output match {
          case Append(names: _*) => List.from(names map trVar)
          case NilVal            => Nil
          case x: String         => List(trVar(x))
        }
      }
      val shortcuts = Set.from(shortClauses map {
        // TODO: 以下の警告は consClauses の型を工夫することで回避できるはず
        case (name, (params, ListPattern.Cons(hd, tl)), guard, output) =>
          val (auxParams, intParams) = paramTranslation(params)
          (
            name,
            translateGuard(intParams, guard),
            translateOutput[currPtr.type | restInp.type](Map(hd -> currPtr, tl -> restInp), auxParams, output)
          )
      })
      def makeUpdate(
          head: String,
          auxParams: String => Int,
          nextArgs: Seq[Append | NilVal | String]
      ): expresso.Update[Int, currPtr.type] = Map.from(nextArgs.zipWithIndex map { case (args, x) =>
        x -> translateOutput[currPtr.type](Map(head -> currPtr), auxParams, args)
      })
      def makeImage(intParams: String => Int, nextArgs: Seq[Increment | String]): Map[Int, Int] =
        Map.from(nextArgs map {
          case (sign, name, n) => intParams(name) -> sign(n)
          case name: String    => intParams(name) -> 0
        })
      val transitions = Set.from(transClauses map {
        case (name, (params, ListPattern.Cons(hd, tl)), guard, FunCall(nextName, nextArgs)) =>
          val (auxParams, intParams) = paramTranslation(params)
          // require(??? /* nextArgs の正しい位置に tl がある */ )
          // require(??? /* nextArgs の型の並びと auxFunArgs の並びが同じ */ )
          val (nextAuxs, nextInts) =
            nextArgs.init.partitionMap[Append | NilVal | String, Increment | String] {
              case x: (Append | NilVal)                  => Left(x)
              case x: Increment                          => Right(x)
              case x: String if auxParams.isDefinedAt(x) => Left(x)
              case x: String if intParams.isDefinedAt(x) => Right(x)
            }
          // require(??? /* nextInts は intParams の順に並んでいる */ )
          (
            name,
            translateGuard(intParams, guard),
            makeUpdate(hd, auxParams, nextAuxs),
            makeImage(intParams, nextInts),
            nextName
          )
      })

      GuardedSDST_withShortcuts(
        types,
        GuardedSDST(
          types,
          states,
          initialState,
          listVars,
          labels,
          params,
          initialParikhImage,
          transitions,
          outputFunction
        ),
        shortcuts
      )
    }

  private class GuardedSDST_withShortcuts_Impl[Q, X, L](
      types: GuardedTypes[Q, X, L],
      override val sdst: types.MachineWithoutShortcuts,
      override val shortcuts: Set[types.Shortcut]
  ) extends GuardedSDST_withShortcuts

  def apply[Q, X, L](
      types: GuardedTypes[Q, X, L],
      sdst: types.MachineWithoutShortcuts,
      shortcuts: Set[types.Shortcut],
  ): GuardedSDST_withShortcuts { type State = Q; type ListVar = X; type ParikhLabel = L } =
    GuardedSDST_withShortcuts_Impl(
      types,
      sdst,
      shortcuts
    )
}

private class Counter private (initial: Int) {
  private var count = initial
  def get           = count
  def add1          = { count += 1; count }
}

private object Counter {
  def apply(initial: Int): Counter = new Counter(initial)
}

private object ParikhImage {
  def zeros[L](labels: Set[L]): Map[L, Int] = labels.map(_ -> 0).toMap
}

private abstract class GuardedSDST {

  import CurrOrDelim.curr

  /// abstract members & concrete types
  type State
  type ListVar
  type ParikhLabel
  type Update      = expresso.Update[ListVar, curr.type]
  type ParikhImage = Map[ParikhLabel, Int] // 負でも良い
  type ParamTerm   = Presburger.Term[Param]
  type Guard       = Map[ParikhLabel, (Inequal, ParamTerm)]
  type Edge        = (State, Guard, Update, ParikhImage, State)
  type Param       = String                // needs to be String by SDST2 definition
  val states: Set[State]
  val initialState: State
  val listVars: Set[ListVar]
  val labels: Set[ParikhLabel]
  val params: Set[Param]
  val initialParikhImage: Map[ParikhLabel, ParamTerm] // 拡張 Parikh 像の仮想的な初期値
  val transitions: Set[Edge]
  val outputFunction: Map[State, Seq[ListVar]]

  /// concrete menber
  def srcOf(e: Edge): State         = e._1
  def dstOf(e: Edge): State         = e._5
  def guardOf(e: Edge): Guard       = e._2
  def updateOf(e: Edge): Update     = e._3
  def imageOf(e: Edge): ParikhImage = e._4

  override def toString(): String =
    s"states=${states}" ++
      s"initialState=${initialState}" ++
      s"listVars=${listVars}" ++
      s"labels=${labels}" ++
      s"params=${params}" ++
      s"initialParikhImage=${initialParikhImage}" ++
      s"transitions=${transitions}" ++
      s"outputFunction=${outputFunction}"

  // Parikh SDST に変換する
  def toSDST: SimpleStreamingDataStringTransducer2 = {
    // まず仮定のチェックとその witness を計算する。
    // characteristics(l) = (prior, posterior)
    // prior, posteriror はそれぞれ組 (states, image, guard) で、
    // states に至る遷移のガードが guard かつ Parikh 像の l 成分が image.
    val characteristics =
      labels.map { (lab: ParikhLabel) =>
        // 状態空間をガードと Parikh 像で分類する
        val grp = transitions.groupMap(t => (guardOf(t)(lab), imageOf(t)(lab)))(dstOf).toList
        // ちょうど2つの類がある
        require(grp.length == 2) // TODO: mitigate to grp.length <= 2
        val (prior @ ((priGuard, priImage), priStates), posterior @ ((postGuard, postImage), postStates)) = {
          var List(prior @ (_, priQs), posterior) = grp
          if (!priQs(initialState)) {
            val tmp = prior
            prior = posterior
            posterior = tmp
          }
          (prior, posterior)
        }
        // 確かに分割である
        require((priStates | postStates) == states && (priStates & postStates).isEmpty)
        // 戻る遷移はない
        require(!transitions.exists(t => priStates(dstOf(t)) && postStates(srcOf(t))))
        // 初めは±1、やがて変えなくなる
        require(math.abs(priImage) == 1)
        require(postImage == 0)
        // 不等号の形を確認
        val (priComparator, priBoundary)   = priGuard
        val (postComparator, postBoundary) = postGuard
        require(if (priImage > 0) then priComparator.isLess else !priComparator.isLess)
        require(priComparator.dual == postComparator)
        // 境界値は一致する
        require(priBoundary == postBoundary)
        lab -> ((priStates, priImage, priGuard), (postStates, postImage, postGuard))
      }.toMap

    enum Label {
      case P(x: ParikhLabel) // ParikhLabel のコピー
      case S                 // どの状態で終わったかを表す
    }
    val newLabels: Set[Label] = this.labels.map(Label.P(_)) + Label.S
    val stateNumbering        = states.zipWithIndex.toMap
    // Parikh 像を非負にする
    // TODO: types
    val edges = this.transitions
      .map[(State, CurrOrDelim, expresso.Update[ListVar, CurrOrDelim], Map[Label, Int], State)] { e =>
        val src = srcOf(e)
        val absImage =
          imageOf(e).map { case (l, n) => Label.P(l) -> n.abs } + (Label.S -> 0)
        (src, curr, updateOf(e), absImage, dstOf(e))
      }
    // 状態の検出を加える
    val outGraph = outputFunction.map { case (state, w) =>
      val stateVec = newLabels.map(_ -> 0).toMap + (Label.S -> stateNumbering(state))
      val spec     = Cupstar.lift1[ListVar, CurrOrDelim](w)
      (state, spec, stateVec)
    }.toSet
    val formulae = {
      val sugar = new PresburgerFormulaSugarForParikhAutomaton[Param, Label]
      import sugar._
      Monoid.foldMapWith(Presburger.conjunctiveMonoid)(labels) { lab =>
        val ((priorStates, priorImage, (priorInequal, boundary)), (postStates, _, _)) =
          characteristics(lab)
        val increasing = priorImage > 0
        val strict     = priorInequal == Inequal.Gt
        require(!increasing && strict) // TODO: とりあえず動かすための仮定
        val initialLab = initialParikhImage(lab).injected
        val labDiff    = label(Label.P(lab))
        val endedInPrior = Monoid.foldMapWith(Presburger.disjunctiveMonoid)(priorStates) { state =>
          label(Label.S) === stateNumbering(state)
        }
        val resultVal = {
          val op = (e1: Term, e2: Term) =>
            if (increasing) Presburger.Add(Seq[Term](e1, e2))
            else Presburger.Sub(e1, e2) // NOTE: 仮定より今はこれ
          op(initialLab, labDiff)
        }
        val comp: (sugar.Term, sugar.Term) => sugar.Formula =
          if (increasing && strict) Presburger.Lt(_, _)
          else if (increasing && !strict) Presburger.Le(_, _)
          else if (!increasing && strict) Presburger.Gt(_, _) // NOTE: 仮定より今はこれ
          else Presburger.Ge(_, _)
        // TODO: !strict だったら boundary に ±1 がある
        (labDiff === 0 && !comp(initialLab, boundary.injected)) || // 初めからガードが成り立たない
        (resultVal === boundary.injected) ||                       // 初めは prior にいるが、いつか prior から出る
        (endedInPrior && (comp(resultVal, boundary.injected)))     // ずっと prior にいる
      }
    }
    val sst = ParikhSST[State, CurrOrDelim, CurrOrDelim, ListVar, Label, Param](
      states = states,
      inSet = Set(CurrOrDelim.curr),
      xs = listVars,
      ls = newLabels,
      is = params,
      edges = edges,
      q0 = initialState,
      outGraph = outGraph,
      acceptFormulas = Seq(formulae)
    )
    SimpleStreamingDataStringTransducer2[State, ListVar, Label](sst)
  }

}

private object GuardedSDST {
  private class GuardedSDSTImpl[Q, X, L](
      types: GuardedTypes[Q, X, L],
      override val states: Set[Q],
      override val initialState: Q,
      override val listVars: Set[X],
      override val labels: Set[L],
      override val params: Set[String],
      override val initialParikhImage: Map[L, types.ParamTerm],
      override val transitions: Set[types.Transition],
      override val outputFunction: Map[Q, Seq[X]],
  ) extends GuardedSDST {
    type State       = Q
    type ListVar     = X
    type ParikhLabel = L
  }
  def apply[Q, X, L](
      types: GuardedTypes[Q, X, L],
      states: Set[Q],
      initialState: Q,
      listVars: Set[X],
      labels: Set[L],
      params: Set[String],
      initialParikhImage: Map[L, types.ParamTerm],
      transitions: Set[types.Transition],
      outputFunction: Map[Q, Seq[X]],
  ): GuardedSDST {
    type State       = Q
    type ListVar     = X
    type ParikhLabel = L
  } = new GuardedSDSTImpl(
    types,
    states,
    initialState,
    listVars,
    labels,
    params,
    initialParikhImage,
    transitions,
    outputFunction
  )
}
