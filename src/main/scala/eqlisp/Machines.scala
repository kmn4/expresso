package com.github.kmn4.expresso.eqlisp

import com.github.kmn4.expresso
import com.github.kmn4.expresso.Cupstar
import com.github.kmn4.expresso.machine.ParikhAutomaton
import com.github.kmn4.expresso.machine.ParikhSST
import com.github.kmn4.expresso.math.Cop
import com.github.kmn4.expresso.math.Cop1
import com.github.kmn4.expresso.math.Cop2
import com.github.kmn4.expresso.math.Monoid
import com.github.kmn4.expresso.math.Presburger

import collection.mutable.{Map as MMap, Set as MSet}

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

  // 出力関係でデータを出力しない
  require(outputRelation.forall(o => !outputSpecOf(o).exists(x => x == curr)))

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

  def addParamFormulaExtendingParamSet(
      formula: Presburger.Formula[String]
  ): SimpleStreamingDataStringTransducer2 =
    addParamsAndFormula(formula.freeVars, formula)

  def addParamsAndFormula(
      params: Iterable[String],
      formula: Presburger.Formula[String]
  ): SimpleStreamingDataStringTransducer2 = {
    val sugar = new PresburgerFormulaSugarForParikhAutomaton[String, ParikhLabel]
    import sugar._
    val newParamSet = intParams ++ params
    require(formula.freeVars subsetOf newParamSet)
    val formulae = internalSST.acceptFormulas :+ formula.injected
    SimpleStreamingDataStringTransducer2(internalSST =
      internalSST.copy(is = newParamSet, acceptFormulas = formulae)
    )
  }

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
        i   <- 0 until numReadStrings if i != operand
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

  def delim_scheme(
      numReadStrings: Int,
      concatOperands: Option[Seq[Int]],
      preserveList: Int => Boolean = _ => true,
      useLength: Set[Int] = Set(),
  ): (SSDT, Map[Int, String]) = {

    val gen         = ParamGenerator
    val lengthParam = Map.from(useLength map (_ -> gen()))

    // numReadStrings 個のデータリストを区切り文字で区切って並置したものを読む。
    // i 番目のデータリストは状態 i で読む。
    // concatOperands == Some(operands) であるとき、
    // リスト変数 i には operands(i) 番目のデータリストを格納し、
    // operands に登場する順に連接したものを出力に加える。
    // concatOperands == None なら出力しない (末尾の区切り文字も出力されない)。
    // preserveList(i) なら x_{in} に i 番目のデータリストを保存し、
    // これは前記の連接の左に出力される。
    // useLength(i) なら i 番目のデータリストの長さをラベル i でカウントして、
    // 「lengthParam(i): Param === i: Label」 を受理論理式に加える。

    val shouldEmitConcat = concatOperands.nonEmpty
    val operands         = concatOperands.getOrElse(Nil)

    val states   = (0 to numReadStrings).toSet
    val xin      = -1
    val listVars = (xin until operands.length).toSet
    val labels   = Set.from((0 until numReadStrings).filter(useLength))
    val zeros    = ParikhImage.zeros(labels)
    val edges = {
      val id = expresso.Update.identity[Int, CurrOrDelim](listVars)
      def add(spec: (Int, CurrOrDelim)*) =
        id ++ Map.from(spec map { (`var`, sym) => `var` -> List(Cop1(`var`), Cop2(sym)) })
      val delimEdges = for {
        i <- 0 until numReadStrings
      } yield (i, delim, if (preserveList(i)) add(xin -> delim) else add(), zeros, i + 1)
      def inverse(i: Int): Seq[Int] = for ((x, j) <- operands.zipWithIndex if x == i) yield j
      def edgeStoring(i: Int) = {
        val storage     = if (preserveList(i)) inverse(i) :+ xin else inverse(i)
        val update      = add((storage map (_ -> curr)): _*)
        val parikhImage = if (useLength(i)) zeros + (i -> 1) else zeros
        (i, curr, update, parikhImage, i)
      }
      (delimEdges ++ (0 until numReadStrings).map(edgeStoring)).toSet
    }
    val outputRelation = {
      var output: expresso.Cupstar[Int, CurrOrDelim] = List(Cop1(xin))
      if (shouldEmitConcat) output ++= operands.indices.map(Cop1(_)) :+ Cop2(delim: CurrOrDelim)
      Set((numReadStrings, output, zeros))
    }

    val formulae = {
      val sugar = new PresburgerFormulaSugarForParikhAutomaton[String, Int]
      import sugar.{label, param, _}
      Seq.from(useLength map (l => label(l) === param(lengthParam(l))))
    }

    val countSDST: SSDT =
      SSDT(
        ParikhSST(
          states = states,
          inSet = Set(curr, delim),
          xs = listVars,
          ls = labels,
          is = Set.from(lengthParam.values),
          edges = edges,
          q0 = 0,
          outGraph = outputRelation,
          acceptFormulas = formulae
        )
      )

    (countSDST, lengthParam)
  }

  def concatDelim(numReadStrings: Int, operands: Seq[Int]): SSDT =
    delim_scheme(numReadStrings, Some(operands))._1

  // WARN: 今の所 operands.length == 1 じゃないと意図通り動かない (?)
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
  extension (formula: Presburger.Formula[I]) {
    def injected: Formula = formula.renameVars(Left(_))
  }
}

// セマンティクスの定義
object SDSTSemantics {

  class OutputNotDefinedException             extends Exception
  class MultipleOutputExistsException(x: Any) extends Exception

  import CurrOrDelim.{curr, delim}
  type DataOrDelimSeq = Seq[Either[Int, delim.type]]
  def seq(xs: Any*): DataOrDelimSeq = xs.collect {
    case x: Int  => Left(x)
    case `delim` => Right(delim)
  }
  val :# = delim
  def transduce(t: SimpleStreamingDataStringTransducer2, xs: DataOrDelimSeq): DataOrDelimSeq =
    transduce(t, Map(), xs)
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
    if (result.size == 0) throw new OutputNotDefinedException
    else if (result.size >= 2) throw new MultipleOutputExistsException(result)
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
    assert(transduce(machine, Map(nDrop -> 3), seq()) == seq())
    assert(transduce(machine, Map(nDrop -> 0), seq()) == seq())
    assert(transduce(machine, Map(nDrop -> -10), seq()) == seq())
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

  def identity(machine: SimpleStreamingDataStringTransducer2) = {
    assert(transduce(machine, Map.empty, seq(1, 2, 3)) == seq(1, 2, 3))
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

  val takeDrop = DefprogMachines.concatSplit

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
  printTime("func? takeDrop")
  assert(checkFunctionality(takeDrop)) // この場合は 5 分程度で決定できる
  printTime("delimID =equiv? takeDrop")
  assert(checkEquivalence(delimId, takeDrop))
  println("equivalence checking examples done")
}

private trait ParamGenerator { def apply(): String; def gen(): String = apply() }

// TODO: prefix から始まるシンボルをパーサレベルで禁止する
private object ParamGenerator extends ParamGenerator {
  private val used: MSet[String] = MSet.empty
  private val prefix: String     = "_$"
  private val ascii: Array[Char] = Array.from(('A' to 'Z') ++ ('a' to 'z'))
  private def nextASCII(): Char  = ascii(scala.util.Random.nextInt(ascii.length))
  private def randomString(): String = {
    import scala.util.Random
    // 52^6 = 19,770,609,664 通りあれば十分
    val id = List.fill(6)(nextASCII()).mkString
    s"${prefix}${id}"
  }
  def apply(): String = {
    val res = LazyList.from(0).map(_ => randomString()).find(!used(_)).get
    used.add(res)
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
    // NOTE: 定義域の等価性は省略している

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
        // i.e. 同じ出力位置に、データと区切り文字が来る、または両方データでオリジンが異なる
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
      val gen           = ParamGenerator
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
