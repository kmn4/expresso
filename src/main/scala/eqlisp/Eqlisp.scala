package com.github.kmn4.expresso.eqlisp

import com.github.kmn4.expresso
import com.github.kmn4.expresso.Cupstar
import com.github.kmn4.expresso.machine.ParikhSST
import com.github.kmn4.expresso.math.Cop
import com.github.kmn4.expresso.math.Cop1
import com.github.kmn4.expresso.math.Cop2
import com.github.kmn4.expresso.math.Monoid
import com.github.kmn4.expresso.math.Presburger
import com.monovore.decline

import java.io.FileInputStream
import java.io.InputStream
import java.io.SequenceInputStream

import collection.mutable.{Map as MMap, Set as MSet}

/// データリスト操作の等価性問題を記述するためのスクリプト

//// 構文

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

  // NOTE: args の String は整数パラメタかもしれない
  final case class AuxFunCall(name: String, args: Seq[Append | NilVal | Increment | String])

  case class AuxFnClause(
      name: String,
      params: AuxFnParams,
      body: Seq[(Guard, Append | NilVal | String /* リスト変数 */ | AuxFunCall)]
  )

  type AuxFnParams = (Seq[String], ListPattern)

  object NoGuard {
    def apply(x: Append | NilVal | String | AuxFunCall): Seq[(Guard, Append | NilVal | String | AuxFunCall)] =
      List((Guard(Nil), x))
    def unapply(
        xs: Seq[(Guard, Append | NilVal | String | AuxFunCall)]
    ): Option[Append | NilVal | String | AuxFunCall] =
      Option.when(xs.size == 1 && xs.head._1.conjuncts.length == 0)(xs.head._2)
  }

  sealed abstract class ProgramStatement
  final case class Assignment(lhs: String, rhs: FunCall) extends ProgramStatement
  final case class FunCall(name: String, args: Seq[FunCallArithExp | String])

  type FunCallArithExp = FunCallArith.Exp
  object FunCallArith extends AExpBase {
    type exp = this.Exp
    case class Length(name: String) extends this.Exp
    object ArithExp {
      case class Const(n: Int)                    extends Exp.Const(n)
      case class Var(name: String)                extends Exp.Var(name: String)
      case class Mod(divident: exp, divisor: exp) extends Exp.Mod(divident, divisor)
      case class Add(e1: exp, e2: exp)            extends Exp.Add(e1, e2)
      case class Sub(e1: exp, e2: exp)            extends Exp.Sub(e1, e2)
      case class Mul(e1: exp, e2: exp)            extends Exp.Mul(e1, e2)
    }

    export ArithExp._
  }

  extension (self: FunCallArithExp) {
    def toArithExp(renameLength: String => String): ArithExp = {
      def aux(e: FunCallArithExp): ArithExp = e match {
        case FunCallArith.Length(x)   => ArithExp.Var(renameLength(x))
        case FunCallArith.Const(x)    => ArithExp.Const(x)
        case FunCallArith.Var(x)      => ArithExp.Var(x)
        case FunCallArith.Mod(e1, e2) => ArithExp.Mod(aux(e1), aux(e2))
        case FunCallArith.Add(e1, e2) => ArithExp.Add(aux(e1), aux(e2))
        case FunCallArith.Sub(e1, e2) => ArithExp.Sub(aux(e1), aux(e2))
        case FunCallArith.Mul(e1, e2) => ArithExp.Mul(aux(e1), aux(e2))
      }
      aux(self)
    }
    def lengthCallArgs: Set[String] = {
      def aux(e: FunCallArithExp): Set[String] = e match {
        case FunCallArith.Length(x)   => Set(x)
        case FunCallArith.Const(x)    => Set.empty
        case FunCallArith.Var(x)      => Set.empty
        case FunCallArith.Mod(e1, e2) => aux(e1) ++ aux(e2)
        case FunCallArith.Add(e1, e2) => aux(e1) ++ aux(e2)
        case FunCallArith.Sub(e1, e2) => aux(e1) ++ aux(e2)
        case FunCallArith.Mul(e1, e2) => aux(e1) ++ aux(e2)
      }
      aux(self)
    }
  }

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
    private val lengthMeasuredVars: Set[String] = Set.from {
      def collect(args: Seq[FunCallArithExp | String]): Seq[String] = args flatMap {
        case x: FunCallArithExp => x.lengthCallArgs
        case _: String          => Set.empty
      }
      body flatMap { case Assignment(_, FunCall(_, args)) => collect(args) }
    }
    // 中間生成リストや出力リストとして指定された通りの順に、その値が定義される
    require(((intermidiateLists ++ Seq(outputList)) zip definedListNames).forall(_ == _))
    def makeSDST(
        env: String => Seq[String] => SimpleStreamingDataStringTransducer2
    ): SimpleStreamingDataStringTransducer2 = {

      // counter: 区切られた出力リストを読んでカウントする SDST
      // _lengthParamName(i): i 番目のリストの長さが束縛されるパラメータ
      // lengthParamName(x): 変数 x のリストの長さが束縛されるパラメータ
      // NOTE: lengthMeasuredVars.isEmpty なら不要
      val (counter, _lengthParamName) =
        SimpleStreamingDataStringTransducer2.delim_scheme(
          numReadStrings = listNames.length,
          concatOperands = None,
          useLength = lengthMeasuredVars map nthListName
        )
      val lengthParamName: Map[String, String] =
        _lengthParamName map { case (idx, name) => listNames(idx) -> name }
      val lengthParamNames: Set[String] = Set.from(lengthParamName.values)

      val delimitedStringTransducers: Seq[SimpleStreamingDataStringTransducer2] =
        body.zipWithIndex map { case (Assignment(definedVar, FunCall(funName, funArgs)), idxStatement) =>
          val numReadStrings = 1 /* inputList */ + idxStatement
          if (funName == "++") // TODO: 特別扱いされるべき関数が他にないか考える
            SimpleStreamingDataStringTransducer2
              .concatDelim(
                numReadStrings = numReadStrings,
                // TODO: 実行時チェックをちゃんとやる
                operands = funArgs.asInstanceOf[Seq[String]] map nthListName
              )
          else {

            // 関数呼び出しの引数が算術論理式 exp ならば、
            // 名前 name を生成して、構成される SDST にパラメータとして name を、
            // 受理論理式として exp === name を追加する。
            // exp 内の (length x) は lengthParamName(x) に置き換えられる。

            val (intArgs, freshNameOpts, formulaOpts) = funArgs.init.map {
              case x: String => (x, Option.empty, Option.empty)
              case exp: FunCallArithExp =>
                import Presburger.{Eq, Var}
                val name               = ParamGenerator.gen()
                val arithExp: ArithExp = exp.toArithExp(lengthParamName)
                (name, Option(name), Option(Eq(arithExp.toPresburgerTerm, Var(name))))
            }.unzip3
            val freshNames        = freshNameOpts.flatten
            val conjunction       = Presburger.Conj(formulaOpts.flatten)
            val listInput: String = funArgs.last.asInstanceOf[String] // TODO: 実行時チェックをちゃんとやる
            SimpleStreamingDataStringTransducer2
              .liftDelim(
                env(funName)(intArgs),
                numReadStrings = numReadStrings,
                operand = nthListName(listInput)
              )
              .addParamsAndFormula(freshNames ++ lengthParamNames, conjunction)
          }
        }
      val projection =
        SimpleStreamingDataStringTransducer2
          .projection(numReadStrings = listNames.length, operands = Seq(nthListName(outputList)))
      // TODO: lengthMeasuredVars.isEmpty なら counter は不要
      val transducers = delimitedStringTransducers ++ Seq(counter) ++ Seq(projection)
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

}

//// REPL

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

  val auxFunCall: SListParser[AuxFunCall] = {
    val increment: SListParser[Increment] = {
      val plus  = funcall("+")((symbol * int) map { case (name, value) => (Sign.Plus, name, value) })
      val minus = funcall("-")((symbol * int) map { case (name, value) => (Sign.Minus, name, value) })
      plus | minus
    }
    val arg = append | nil | symbol | increment
    list(for {
      name <- symbol
      args <- many(arg)
    } yield AuxFunCall(name, args))
  }

  type AuxFnBody = Append | NilVal | String | AuxFunCall // TODO: InputFormat に移動
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

  val funCallArith: SListParser[FunCallArithExp] = new SListParser[FunCallArith.Exp] {
    val length   = funcall("length")(symbol map FunCallArith.Length.apply)
    val variable = symbol map (name => FunCallArith.Var(name))
    val const    = int map FunCallArith.Const.apply
    def bop(xs: Seq[SExpr]) = {
      val p = unionMap(
        "+"   -> FunCallArith.Add.apply,
        "-"   -> FunCallArith.Sub.apply,
        "*"   -> FunCallArith.Mul.apply,
        "mod" -> FunCallArith.Mod.apply,
      ) { case (op, construct) => funcall(op)((this * this) map (construct(_, _))) }
      p(xs)
    }
    def apply(xs: Seq[SExpr]) = length(xs) ++ variable(xs) ++ const(xs) ++ bop(xs)
  }

  val progFunCall: SListParser[FunCall] = list(for {
    name <- symbol
    args <- many(symbol | funCallArith)
  } yield FunCall(name, args))

  val assignment: SListParser[Assignment] = list(for {
    _   <- keyword("=")
    lhs <- symbol
    rhs <- progFunCall
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
  val assumptions: SListParser[Seq[Assumption]] = many(list(for {
    comp <- comparator
    lhs  <- assumptionExp
    rhs  <- assumptionExp
  } yield Assumption(comp, lhs, rhs)))

  val equiv: SListParser[Command] = list {
    for {
      _           <- constSymbol("equiv?!")
      name1       <- symbol
      name2       <- symbol
      assumptions <- optionSeq(keywordArgs("assumption")(assumptions))
    } yield CheckEquiv(name1, name2, assumptions)
  }

  def read[A](p: SListParser[A])(xs: Seq[SExpr]): Option[A] = p.parse(xs)

  val readCommand: SExpr => Option[Command] = read(defop | defprog | equiv) compose (x => ParserSeqImpl(x))

  import smtlib.parser.ParserCommon
  import smtlib.lexer.Lexer

  class SExprParser(val lexer: Lexer) extends ParserCommon {
    def current = peekToken
    def parseAllSExpr = ParserSeqImpl.unfold(current) { token =>
      if (token != null) Option((parseSExpr, current))
      else None
    }
  }

}

private class Reader(private val reader: java.io.Reader) {

  import smtlib.lexer.Lexer
  import InputFormat.Command

  private val parser = new Reader.SExprParser(new Lexer(reader))

  // private def readSExpr = parser.parseSExpr
  private def readSExpr = Option.when(parser.current != null)(parser.parseSExpr)

  // 失敗したら例外を投げる
  def apply(): Option[Command] = readSExpr map (x => Reader.readCommand(x).get)

}

private object ReaderRunner {

  export Reader._

  import smtlib.parser.ParserCommon
  import smtlib.lexer.Lexer

  def parseAllSExpr(w: String) = {
    val reader = new java.io.StringReader(w)
    val parser = new Reader.SExprParser(new Lexer(reader))
    parser.parseAllSExpr
  }

  def read[A](p: SListParser[A])(code: String): Option[A] = read(p)(parseAllSExpr(code))

  def readAndPrint[A](p: SListParser[A])(code: String): Unit = {
    println(";;; read")
    println(code)
    println(";;; result")
    println(read(p)(code))
  }

}

private object ReaderExamples extends App {

  import ReaderRunner._
  import InputCodeExamples._

  readAndPrint(defop)(code = defop_take)
  readAndPrint(defop)(code = defop_drop)
  readAndPrint(defop)(code = defop_identity)
  readAndPrint(defprog)(defprog_concatSplit)
  readAndPrint(equiv)(equiv_concatSplit_identity)

}

private class Evaluator {

  import InputFormat._

  private val sdstScheme      = MMap.empty[String, Seq[String] => SimpleStreamingDataStringTransducer2]
  private[eqlisp] val sdstEnv = MMap.empty[String, SimpleStreamingDataStringTransducer2]

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

  def checkEquiv(
      t1: SimpleStreamingDataStringTransducer2,
      t2: SimpleStreamingDataStringTransducer2,
      assumptions: Seq[Assumption]
  ) = {
    if (Evaluator.checkEquiv(t1, t2, assumptions)) println("equivalent")
    else println("not equivalent")
  }

  // for tests and debugging

  def makeSDST(name: String, paramNames: String*): SimpleStreamingDataStringTransducer2 =
    sdstScheme(name)(paramNames)

  def getSDST(name: String): SimpleStreamingDataStringTransducer2 = sdstEnv(name)

}

private object Evaluator {

  import InputFormat._
  import DataStringTheory2.compose

  val sugar = new PresSugar[String]
  import sugar._

  def checkEquiv(
      t1: SimpleStreamingDataStringTransducer2,
      t2: SimpleStreamingDataStringTransducer2,
      assumptions: Seq[Assumption]
  ): Boolean = {
    if (assumptions.isEmpty) return DataStringTheory2.checkEquivalence(t1, t2)

    // 入力リストのデータ数をカウントするトランスデューサを左から合成する

    val params = t1.intParams ++ t2.intParams
    // TODO: defprog の :input が複数な場合を許すなら以下も修正する
    val nInputLists = 1
    val (count, _lengthParam) =
      SimpleStreamingDataStringTransducer2.delim_scheme(
        numReadStrings = nInputLists,
        concatOperands = None,
        useLength = Set(0),
      ): @unchecked
    val lengthParam  = _lengthParam(0)
    val t1WithLength = compose(count, t1)
    val t2WithLength = compose(count, t2)

    // カウント情報を使って assumptions に相当する論理式を付け加える

    extension (self: Assumption.Exp) {
      def toArithExp(lengthVarName: String): ArithExp = self match {
        case Assumption.Length    => ArithExp.Var(lengthVarName)
        case Assumption.Const(n)  => ArithExp.Const(n)
        case Assumption.Var(name) => ArithExp.Var(name)
        case Assumption.Add(e1, e2) =>
          ArithExp.Add(e1.toArithExp(lengthVarName), e2.toArithExp(lengthVarName))
        case Assumption.Sub(e1, e2) =>
          ArithExp.Sub(e1.toArithExp(lengthVarName), e2.toArithExp(lengthVarName))
        case Assumption.Mod(e1, e2) =>
          ArithExp.Mod(e1.toArithExp(lengthVarName), e2.toArithExp(lengthVarName))
        case Assumption.Mul(e1, e2) =>
          ArithExp.Mul(e1.toArithExp(lengthVarName), e2.toArithExp(lengthVarName))
      }
    }

    val assumptionFormula: Formula = Monoid.foldMap(assumptions) { case Assumption(comparator, lhs, rhs) =>
      val lterm = lhs.toArithExp(lengthParam).toPresburgerTerm
      val rterm = rhs.toArithExp(lengthParam).toPresburgerTerm
      val makeFormula: (Term, Term) => Formula = comparator match {
        case Equal      => Presburger.Eq(_, _)
        case Inequal.Ge => Presburger.Ge(_, _)
        case Inequal.Gt => Presburger.Gt(_, _)
        case Inequal.Le => Presburger.Le(_, _)
        case Inequal.Lt => Presburger.Lt(_, _)
      }
      makeFormula(lterm, rterm)
    }(Presburger.conjunctiveMonoid)

    DataStringTheory2.checkEquivalence(
      t1WithLength.addParamFormulaExtendingParamSet(assumptionFormula),
      t2WithLength.addParamFormulaExtendingParamSet(assumptionFormula)
    )
  }
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

  def interpretAllSilently(is: java.io.InputStream): REPL = {
    val repl = REPL(is)
    repl.setOptions(REPL.Options(print = false))
    repl.interpretAll()
    repl
  }

  case class Options(print: Boolean = true)
}

object Eqlisp
    extends decline.CommandApp(
      name = "eqlisp",
      header = "decide equivalence of list programs",
      main = {
        import decline._
        import java.nio.file.Path
        // 複数ファイルを指定可能。
        // 省略されていたら標準入力。
        val inputStream: Opts[InputStream] = Opts
          .arguments[Path]("script file")
          .orNone
          .map {
            case Some(filePaths) =>
              filePaths
                .map[InputStream](path => new FileInputStream(path.toFile()))
                .reduceLeft(new SequenceInputStream(_, _))
            case None => System.in
          }
        inputStream map (is => REPL(is).interpretAll())
      }
    )

object InputCodeStreams {
  def fromFile(name: String): InputStream = new FileInputStream(name)

  def funcs = fromFile("./eqlisp/funcs.eql")
  def progs = fromFile("./eqlisp/progs.eql")

}

extension (self: InputStream) {
  def ++(that: InputStream): InputStream = new SequenceInputStream(self, that)
}

object DefopMachines {

  val repl = REPL.interpretAllSilently(InputCodeStreams.funcs)

  def take(i: String) = repl.makeSDST("take", i)
  def drop(i: String) = repl.makeSDST("drop", i)
  val takeEven        = repl.makeSDST("take-even")
  val reverse         = repl.makeSDST("reverse")
  val identity        = repl.makeSDST("identity")

}

object DefprogMachines {

  val repl = REPL.interpretAllSilently(InputCodeStreams.funcs ++ InputCodeStreams.progs)

  val concatSplit      = repl.getSDST("concat-split")
  val identity         = repl.getSDST("identity")
  val takeEven_reverse = repl.getSDST("te-rev")
  val reverse_takeEven = repl.getSDST("rev-te")
  val dropDrop         = repl.getSDST("drop-drop")
  val dropSum          = repl.getSDST("drop-sum")
  val dropReverse      = repl.getSDST("drop-reverse")
  val reverseTake      = repl.getSDST("reverse-take")
  val takeAll          = repl.getSDST("take-all")

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
            AuxFunCall("t", List(Append("acc", "x"), (Sign.Minus, "n", 1), "xs"))
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
            AuxFunCall("rec", List("acc", (Sign.Minus, "n", 1), "xs"))
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
        NoGuard(AuxFunCall("te1", List("acc", "xs")))
      ),
      AuxFnClause("te1", (List("acc"), ListPattern.Nil), NoGuard("acc")),
      AuxFnClause(
        "te1",
        (List("acc"), ListPattern.Cons("x", "xs")),
        NoGuard(AuxFunCall("te0", List(Append("acc", "x"), "xs")))
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

//// スクリプトから SDST への変換

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
          case Cop2(`currPtr`) => NewListVar.Curr(cntCurr.add1)
          case Cop2(`restInp`) => NewListVar.Rest(cntRest.add1)
          case Cop1(x)         => x.injected
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
          case x: AuxFunCall                 => Left(cls.copy(_4 = x))
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
        case (name, (params, ListPattern.Cons(hd, tl)), guard, AuxFunCall(nextName, nextArgs)) =>
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

  // requirements

  private def isTotal(guard: Guard) = guard.keySet == labels

  require(transitions forall (isTotal compose guardOf)) // ガードは labels の全ての要素に定義される

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
