package com.github.kmn4.expresso.math

import com.microsoft.z3

object Presburger {

  def eucMod(m: Int, n: Int): Int = (if (m < 0) m % n + math.abs(n) else m % math.abs(n))

  /** Types and constructers for Presburger formula */
  sealed trait Term[X] {
    def eval(valuation: Map[X, Int]): Int = this match {
      case Const(i)    => i
      case Var(x)      => valuation(x)
      case Add(ts)     => ts.map(_.eval(valuation)).sum
      case Sub(t1, t2) => t1.eval(valuation) - t2.eval(valuation)
      case Mult(i, t)  => i.eval(valuation) * t.eval(valuation)
      case Mod(t1, t2) => eucMod(t1.eval(valuation), t2.eval(valuation))
    }

    def freeVars: Set[X] = this match {
      case Var(x) => Set(x)
      case _      => Set.empty
    }

    def size: Int = this match {
      case Const(i)    => 0
      case Var(x)      => 0
      case Add(ts)     => ts.map(_.size).sum + 1
      case Sub(t1, t2) => t1.size + t2.size + 1
      case Mult(c, t)  => c.size + t.size + 1
      case Mod(t1, t2) => t1.size + t2.size + 1
    }
  }
  case class Const[X](i: Int) extends Term[X]
  case class Var[X](x: X) extends Term[X]
  case class Add[X](ts: Seq[Term[X]]) extends Term[X]
  case class Sub[X](t1: Term[X], t2: Term[X]) extends Term[X]
  // Mult は当初定数倍を意図していたが，その後の変更で任意の掛け算として使われるようになった．
  case class Mult[X](c: Term[X], t: Term[X]) extends Term[X]
  case class Mod[X](t1: Term[X], t2: Term[X]) extends Term[X]
  sealed trait Formula[X] {
    def smtlib: String = Formula.formulaToSMTLIB(this)

    def renameVars[Y](renamer: X => Y): Formula[Y] = Formula.renameVars(this)(renamer)

    def freeVars: Set[X] = this match {
      case f: Connective[X] => f.process(_.flatMap(_.freeVars).toSet)
      case Eq(t1, t2)       => t1.freeVars ++ t2.freeVars
      case Lt(t1, t2)       => t1.freeVars ++ t2.freeVars
      case Le(t1, t2)       => t1.freeVars ++ t2.freeVars
      case f: Quantified[X] => f.process { case (vs, f) => f.freeVars -- vs.map(_.x) }
    }

    def boundVars: Set[X] = this match {
      case Top() | Bot() | Eq(_, _) | Lt(_, _) | Le(_, _) => Set.empty
      case Conj(fs)                                       => fs.flatMap(_.boundVars).toSet
      case Disj(fs)                                       => fs.flatMap(_.boundVars).toSet
      case Not(f)                                         => f.boundVars
      case f: Quantified[X] => f.process { case (vs, f) => f.boundVars ++ vs.map(_.x) }
    }

    /** @throws java.lang.UnsupportedOperationException if this contains Exists. */
    def eval(valuation: Map[X, Int]): Boolean = this match {
      case Top()      => true
      case Bot()      => false
      case Eq(t1, t2) => t1.eval(valuation) == t2.eval(valuation)
      case Lt(t1, t2) => t1.eval(valuation) < t2.eval(valuation)
      case Le(t1, t2) => t1.eval(valuation) <= t2.eval(valuation)
      case Conj(fs)   => fs.find(!_.eval(valuation)).isEmpty
      case Disj(fs)   => fs.find(_.eval(valuation)).nonEmpty
      case Not(f)     => !f.eval(valuation)
      case Exists(_, _) | Forall(_, _) =>
        throw new UnsupportedOperationException("Cannot evaluate formula with quantifier.")
    }

    def size: Int = this match {
      case f: Connective[X] => f.process(_.map(_.size).sum + 1)
      case Eq(t1, t2)       => t1.size + t2.size + 1
      case Lt(t1, t2)       => t1.size + t2.size + 1
      case Le(t1, t2)       => t1.size + t2.size + 1
      case f: Quantified[X] => f.process { case (vs, f) => vs.map(_.size).sum + f.size + 1 }
    }
  }
  sealed abstract class Connective[X] extends Formula[X] {
    protected def fs: Seq[Formula[X]]
    def process[Y](op: Seq[Formula[X]] => Y): Y = op(fs)
  }
  case class Top[X]() extends Connective[X] { protected def fs: Seq[Formula[X]] = Seq() }
  case class Bot[X]() extends Connective[X] { protected def fs: Seq[Formula[X]] = Seq() }
  case class Eq[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Lt[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  case class Le[X](t1: Term[X], t2: Term[X]) extends Formula[X]
  def Gt[X](t1: Term[X], t2: Term[X]): Formula[X] = Lt(t2, t1)
  def Ge[X](t1: Term[X], t2: Term[X]): Formula[X] = Le(t2, t1)
  case class Conj[X](fs: Seq[Formula[X]]) extends Connective[X]
  case class Disj[X](fs: Seq[Formula[X]]) extends Connective[X]
  case class Not[X](f: Formula[X]) extends Connective[X] { protected def fs: Seq[Formula[X]] = Seq(f) }
  def Implies[X](pre: Formula[X], post: Formula[X]): Formula[X] = Disj(Seq(Not(pre), post))
  def Equiv[X](f1: Formula[X], f2: Formula[X]): Formula[X] = Conj(Seq(Implies(f1, f2), Implies(f2, f1)))
  sealed abstract class Quantified[X] extends Formula[X] {
    def vs: Seq[Var[X]]
    def f: Formula[X]
    protected def make[Y]: (Seq[Var[Y]], Formula[Y]) => Quantified[Y]
    def transform[Y](op: (Seq[Var[X]], Formula[X]) => (Seq[Var[Y]], Formula[Y])): Quantified[Y] = {
      val (newVs, newF) = op(vs, f)
      make(newVs, newF)
    }
    def process[Y](op: (Seq[Var[X]], Formula[X]) => Y): Y = op(vs, f)
  }
  case class Exists[X](vs: Seq[Var[X]], f: Formula[X]) extends Quantified[X] {
    protected def make[Y] = Exists.apply
  }
  case class Forall[X](vs: Seq[Var[X]], f: Formula[X]) extends Quantified[X] {
    protected def make[Y] = Forall.apply
  }

  object Term {
    def termToSMTLIB[X](t: Term[X]): String = t match {
      case Const(i)     => i.toString()
      case Var(x)       => x.toString()
      case Add(ts)      => s"""(+ 0 ${ts.map(termToSMTLIB).mkString(" ")})"""
      case Sub(t1, t2)  => s"(- ${termToSMTLIB(t1)} ${termToSMTLIB(t2)})"
      case Mult(t1, t2) => s"(* ${termToSMTLIB(t1)} ${termToSMTLIB(t2)})"
      case Mod(t1, t2)  => s"(% ${termToSMTLIB(t1)} ${termToSMTLIB(t2)})"
    }
  }

  object Formula {
    // 代入前後の変数の型は同じでなければならない．
    // ∃x φ(x) が与えられた時 φ(x) について再帰することを考える．
    // φ だけみると x が束縛変数かどうかはわからない．
    // そのため x => if (bounded(x)) Var(x) else subst(x) を新しい subst にして再帰する．
    // 代入前後の型が異なると, then 節をどうすればよいか困る．
    def substitute[X](f: Formula[X])(subst: X => Term[X]): Formula[X] =
      substituteBound(f)(x => subst(x))(identity(_))

    // 束縛変数は substBound で代入する
    // 定義されていなかったら実行時エラーになる
    def substituteBound[X, Y](
        f: Formula[X]
    )(subst: PartialFunction[X, Term[Y]])(substBound: PartialFunction[X, Y]): Formula[Y] = {
      def tm(t: Term[X]): Term[Y] = {
        def aux(t: Term[X]): Term[Y] = t match {
          case Const(i)    => Const(i)
          case Var(x)      => subst(x)
          case Add(ts)     => Add(ts.map(aux))
          case Sub(t1, t2) => Sub(aux(t1), aux(t2))
          case Mult(i, t)  => Mult(aux(i), aux(t))
          case Mod(t1, t2) => Mod(aux(t1), aux(t2))
        }
        aux(t)
      }
      def aux(f: Formula[X]): Formula[Y] = f match {
        case Top()      => Top()
        case Bot()      => Bot()
        case Eq(t1, t2) => Eq(tm(t1), tm(t2))
        case Lt(t1, t2) => Lt(tm(t1), tm(t2))
        case Le(t1, t2) => Le(tm(t1), tm(t2))
        case Conj(fs)   => Conj(fs.map(aux))
        case Disj(fs)   => Disj(fs.map(aux))
        case Not(f)     => Not(aux(f))
        case f: Quantified[X] =>
          f.transform { case (xs, f) =>
            val ys = xs.map { case Var(x) => Var(substBound(x)) }
            val bounded = xs.map { case Var(x) => x }.toSet
            val newSubst: PartialFunction[X, Term[Y]] = {
              case x if bounded(x) => Var(substBound(x))
              case x               => subst(x)
            }
            (ys, substituteBound(f)(newSubst)(substBound))
          }
      }
      aux(f)
    }

    // B: 束縛出現するかもしれない型
    // F: 束縛出現しないことが保証されている型
    // N: F の変換後
    def substituteFreeVars[F, B, N](
        f: Formula[Either[B, F]]
    )(subst: F => Term[Either[B, N]]): Formula[Either[B, N]] = {
      substituteBound(f) {
        case Left(b)     => Var(Left(b): Either[B, N])
        case Right(free) => subst(free)
      } { case Left(b) => Left(b): Either[B, N] }

    }
    // NOTE renamer should be injective
    def renameVars[X, Y](f: Formula[X])(renamer: X => Y): Formula[Y] = {
      def tm(t: Term[X]): Term[Y] = {
        def aux(t: Term[X]): Term[Y] = t match {
          case Const(i)    => Const(i)
          case Var(x)      => Var(renamer(x))
          case Add(ts)     => Add(ts.map(aux))
          case Sub(t1, t2) => Sub(aux(t1), aux(t2))
          case Mult(i, t)  => Mult(aux(i), aux(t))
          case Mod(t1, t2) => Mod(aux(t1), aux(t2))
        }
        aux(t)
      }
      def aux(f: Formula[X]): Formula[Y] = f match {
        case Top()      => Top()
        case Bot()      => Bot()
        case Eq(t1, t2) => Eq(tm(t1), tm(t2))
        case Lt(t1, t2) => Lt(tm(t1), tm(t2))
        case Le(t1, t2) => Le(tm(t1), tm(t2))
        case Conj(fs)   => Conj(fs.map(aux))
        case Disj(fs)   => Disj(fs.map(aux))
        case Not(f)     => Not(aux(f))
        case formula: Quantified[X] =>
          formula.transform { case (xs, f) => (xs.map { case Var(x) => Var(renamer(x)) }, aux(f)) }
      }
      aux(f)
    }
    def formulaToSMTLIB[X](f: Formula[X]): String = f match {
      case Top()      => "(= 0 0)"
      case Bot()      => "(= 0 1)"
      case Eq(t1, t2) => s"(= ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Lt(t1, t2) => s"(< ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Le(t1, t2) => s"(<= ${Term.termToSMTLIB(t1)} ${Term.termToSMTLIB(t2)})"
      case Conj(fs) => {
        val fsString = fs.map(formulaToSMTLIB).mkString(" ")
        s"(and true $fsString)"
      }
      case Disj(fs) => {
        val fsString = fs.map(formulaToSMTLIB).mkString(" ")
        s"(or false $fsString)"
      }
      case Not(f) => s"(not ${formulaToSMTLIB(f)})"
      case Exists(xs, f) => {
        val xsString = xs.map { case Var(x) => s"(${x.toString()} Int)" }.mkString(" ")
        s"(exists (${xsString}) ${formulaToSMTLIB(f)})"
      }
      case Forall(xs, f) => {
        val xsString = xs.map { case Var(x) => s"(${x.toString()} Int)" }.mkString(" ")
        s"(forall (${xsString}) ${formulaToSMTLIB(f)})"
      }
    }

    /** Convert a given formula to z3.BoolExpr. */
    def formulaToZ3Expr[X](
        ctx: z3.Context,
        freeVars: Map[X, z3.IntExpr],
        f: Formula[X]
    ): z3.BoolExpr = {
      var varMap = freeVars
      val trueExpr = ctx.mkBool(true)
      val falseExpr = ctx.mkBool(false)
      def newVar(x: X): z3.IntExpr = {
        val e = ctx.mkIntConst(x.toString())
        varMap += (x -> e)
        e
      }
      def fromTerm(t: Term[X]): z3.ArithExpr[z3.IntSort] = t match {
        case Const(i)    => ctx.mkInt(i)
        case Var(x)      => varMap.getOrElse(x, newVar(x))
        case Add(ts)     => ctx.mkAdd(ts.map(fromTerm): _*)
        case Sub(t1, t2) => ctx.mkSub(fromTerm(t1), fromTerm(t2))
        case Mult(c, t)  => ctx.mkMul(fromTerm(c), fromTerm(t))
        case Mod(t1, t2) => ctx.mkMod(fromTerm(t1), fromTerm(t2))
      }
      def fromFormula(f: Formula[X]): z3.BoolExpr = f match {
        case Top()      => trueExpr
        case Bot()      => falseExpr
        case Eq(t1, t2) => ctx.mkEq(fromTerm(t1), fromTerm(t2))
        case Lt(t1, t2) => ctx.mkLt(fromTerm(t1), fromTerm(t2))
        case Le(t1, t2) => ctx.mkLe(fromTerm(t1), fromTerm(t2))
        case Conj(fs)   => ctx.mkAnd(fs.map(fromFormula): _*)
        case Disj(fs)   => ctx.mkOr(fs.map(fromFormula): _*)
        case Not(f)     => ctx.mkNot(fromFormula(f))
        case Exists(vs, f) => {
          val xs = vs.map { case Var(x) => newVar(x) }
          val body = formulaToZ3Expr(ctx, varMap, f)
          ctx.mkExists(xs.toArray, body, 0, null, null, null, null)
        }
        case Forall(vs, f) => {
          val xs = vs.map { case Var(x) => newVar(x) }
          val body = formulaToZ3Expr(ctx, varMap, f)
          ctx.mkForall(xs.toArray, body, 0, null, null, null, null)
        }
      }
      fromFormula(f)
    }
  }

  object Sugar {
    implicit def const[X](i: Int): Term[X] = Const(i)
    implicit class TermOps[X](t: Term[X]) {
      def +(s: Term[X]): Term[X] = Add(Seq(t, s))
      def -(s: Term[X]): Term[X] = Sub(t, s)
      def *(i: Int): Term[X] = Mult(Const(i), t)
      def ===(s: Term[X]): Formula[X] = Eq(t, s)
      def <(s: Term[X]): Formula[X] = Lt(t, s)
      def <=(s: Term[X]): Formula[X] = Le(t, s)
      def >(s: Term[X]): Formula[X] = Gt(t, s)
      def >=(s: Term[X]): Formula[X] = Ge(t, s)
      def !==(s: Term[X]): Formula[X] = !(t === s)
    }
    implicit class FormulaOps[X](f: Formula[X]) {
      def unary_! : Formula[X] = Not(f)
      def &&(g: Formula[X]): Formula[X] = Conj(Seq(f, g))
      def ||(g: Formula[X]): Formula[X] = Disj(Seq(f, g))
      def ==>(g: Formula[X]): Formula[X] = Implies(f, g)
    }
  }
}
