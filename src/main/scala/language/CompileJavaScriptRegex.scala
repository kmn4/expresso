package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.machine._
import com.github.kmn4.expresso.math.MonadPlus.MonadPlusOps
import com.github.kmn4.expresso.math._
import com.github.kmn4.expresso.Cupstar
import com.github.kmn4.expresso.Cupstar

object CompileJavaScriptRegex {

  private def derive[A, X, M[_]](
      a: A
  )(e: PCRE[A, X])(implicit mp: MonadPlus[M]): M[(Option[PCRE[A, X]], Update[X, A])] = {
    type RegO   = Option[PCRE[A, X]]
    type Update = com.github.kmn4.expresso.Update[X, A]
    implicit def liftE(e: RegO): (RegO, Update)       = (e, Map())
    implicit def liftM(m: M[RegO]): M[(RegO, Update)] = m >>= { e => mp(liftE(e)) }
    implicit def liftF(f: RegO => M[(RegO, Update)]): (RegO, Update) => M[(RegO, Update)] =
      (exp1, update1) => f(exp1) >>= { case (exp2, update2) => mp((exp2, update1 ++ update2)) }
    e match {
      case PCRE.Empty()   => mp.empty
      case PCRE.Eps()     => mp(None)
      case PCRE.Chars(as) => if (as(a)) mp.apply((Some(PCRE.Eps()), Map())) else mp.empty
      case PCRE.AllChar() => mp.apply((Some(PCRE.Eps()), Map()))
      case PCRE.Cat(e1, e2) =>
        derive(a)(e1) >>= {
          case (Some(e), w) => mp((Some(PCRE.Cat(e, e2)), w))
          case (None, w)    => derive(a)(e2) >>= { case (e, u) => mp(e, w ++ u) }
        }
      case PCRE.Alt(e1, e2) => derive(a)(e1) ++ derive(a)(e2)
      case PCRE.Greedy(e) =>
        val derived =
          derive(a)(e) >>= [(RegO, Update)] {
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.Greedy(e))), w))
            case (None, w)    => mp.empty // JS ではスターの内側が空文字列にマッチしない
          }
        // 展開せず空文字列にマッチさせた場合、内側は `undefined` (JS) になる。
        // 置換文字列の構成で undefined 値が参照されると、空文字列として扱われる。
        val epsMatchUpdate = e.groupVars.map(_ -> Nil).toMap
        derived ++ mp((None, epsMatchUpdate))
      case PCRE.NonGreedy(e) =>
        val derived =
          derive(a)(e) >>= [(RegO, Update)] {
            case (Some(f), w) => mp((Some(PCRE.Cat(f, PCRE.NonGreedy(e))), w))
            case (None, w)    => mp.empty
          }
        val epsMatchUpdate = e.groupVars.map(_ -> Nil).toMap
        mp[(RegO, Update)]((None, epsMatchUpdate)) ++ derived
      case PCRE.Group(e, x) =>
        derive(a)(e) >>= {
          case (Some(e), w) => mp((Some(PCRE.GDeriv(e, x)), w + (x -> List(Cop2(a)))))
          case (None, w)    => mp((None, w + (x -> List.empty)))
        }
      case PCRE.GDeriv(e, x) =>
        derive(a)(e) >>= {
          case (Some(e), w) => mp((Some(PCRE.GDeriv(e, x)), w + (x -> List(Cop1(x), Cop2(a)))))
          case (None, w)    => mp((None, w + (x -> List(Cop1(x)))))
        }
    }
  }

  // e に a をマッチさせたときの残りの表現と、a にマッチした部分表現に現れるグループ変数を更新する方法
  // 例えば、(a)* に a をマッチさせると、残りが (a)* で $1 を a で上書きする。
  private def matchOne[A, X, M[_]](e: PCRE[A, X], a: A)(implicit
      mp: MonadPlus[M]
  ): M[(PCRE[A, X], Update[X, A])] = derive(a)(e) >>= {
    case (Some(e), w) => mp((e, w))
    case (None, _)    => mp.empty
  }

  // e を空文字列にマッチさせるとき、e に現れるグループ変数を更新する方法
  private def deriveEps[A, X, M[_]](e: PCRE[A, X])(implicit mp: MonadPlus[M]): M[Update[X, A]] = e match {
    case PCRE.Empty() | PCRE.Chars(_) | PCRE.AllChar() => mp.empty
    case PCRE.Eps()                                    => mp(Map.empty)
    case PCRE.Cat(e1, e2)  => for (w <- deriveEps(e1); u <- deriveEps(e2)) yield w ++ u
    case PCRE.Alt(e1, e2)  => deriveEps(e1) ++ deriveEps(e2)
    case PCRE.Greedy(e)    => mp(Map.empty)
    case PCRE.NonGreedy(e) => mp(Map.empty)
    case PCRE.Group(e, x)  => deriveEps(e).map(_ + (x -> List.empty))
    case PCRE.GDeriv(e, x) => deriveEps(e).map(_ + (x -> List(Cop1(x))))
  }

  def toWholeReplaceSST[A, X](
      e: PCRE[A, X],
      alphabet: Set[A],
      replacement: Cupstar[X, A]
  ): NSST[NonEmptyNub[PCRE[A, X]], A, A, X] = {
    type This = PCRE[A, X]
    // はじめの要素ほど優先度が高い。
    // 状態 [e1, ..., en] は、残りの文字列で en がマッチし、
    // e1, ... e(n-1) は失敗することを推測する。
    type Q = NonEmptyNub[This]
    val q0 = NonEmptyNub(e, Seq.empty)
    def nextStates(q: Q, a: A): Set[(Q, Update[X, A])] = {
      val lowest      = q.last
      val highers     = q.init
      val nextHighers = (highers >>= (matchOne(_, a))).map(_._1).distinct
      val nextLower   = matchOne(lowest, a).distinctBy(_._1)
      var nexts       = Set.empty[(Q, Update[X, A])]
      for (n <- 1 to nextLower.length if !nextHighers.contains(nextLower(n - 1)._1)) {
        val lowerExps = nextLower.take(n).map(_._1)
        val update    = Update.identity(e.groupVars) ++ nextLower(n - 1)._2
        val nextExps  = nextHighers ++ lowerExps
        val nextQ     = NonEmptyNub(nextExps.head, nextExps.tail)
        nexts += ((nextQ, update))
      }
      nexts
    }
    val (states, edges) = searchStates(Set(q0), alphabet)(nextStates)(
      { case (r, _) => r },
      { case (q, a, (r, w)) => (q, a, w, r) }
    )
    val outGraph = for {
      q <- states if q.init.forall(deriveEps(_).isEmpty)
      m <- deriveEps(q.last).headOption
    } yield q -> (Update.identity(e.groupVars) ++ m).subst(replacement)

    NSST(
      states,
      alphabet,
      e.groupVars,
      edges,
      q0,
      graphToMap(outGraph)(identity)
    )
  }

  def toReplaceAllSST[A, X](
      e: PCRE[A, X],
      alphabet: Set[A],
      replacement: Cupstar[X, A]
  ) = {
    // * 基本的な方針 *
    // e0   := (.*?)_{prefixVar} e | (.*)_{botVar}
    // relp := ${prefixVar} replacement
    // 繰り返し e0 にマッチさせ repl に置き換える。
    // マッチがなくなったら最後に botVar の値を出力する。
    // * 最適化 *
    // prefixVar と botVar を SST に持たせる必要はない。
    // prefixVar や botVar に値を加えるときには、
    // 代わりに SST の outputVar に加える。
    type Y   = Either[Int, X]
    type Reg = PCRE[A, Y]
    val prefixVar: Y = Left(-1)
    val botVar: Y    = Left(1)
    val outputVar: Y = Left(2)
    val e0: Reg = PCRE.Alt(
      PCRE.Cat(
        PCRE.Group(PCRE.NonGreedy(PCRE.AllChar()), prefixVar),
        e.renameVars(Right.apply)
      ),
      PCRE.Group(PCRE.Greedy(PCRE.AllChar()), botVar)
    )
    val repl: Cupstar[Y, A] = replacement.map {
      case Cop1(x) => Cop1(Right(x))
      case Cop2(a) => Cop2(a)
    }

    // 以下で SST を構成する
    type Q = NonEmptyNub[Reg]
    val q0: Q           = NonEmptyNub(e0, Nil)
    val sstVars: Set[Y] = e.groupVars.map[Y](Right.apply) + outputVar

    // 補助関数
    type UpdateY = Update[Y, A]
    implicit val uMon: Monoid[UpdateY] = sstVars

    // prefixVar または botVar を x とする。
    // x := x w または x := w であるとき、代わりに
    // outputVar := update(outputVar) w または outputVar := outputVar w とする。
    def simulateWithOutVar(update: UpdateY): UpdateY = {
      assert(!update.isDefinedAt(prefixVar) || !update.isDefinedAt(botVar))
      val x =
        if (update.isDefinedAt(prefixVar)) prefixVar
        else if (update.isDefinedAt(botVar)) botVar
        else return update
      val currentOutput = update.getOrElse(outputVar, List(Cop1(outputVar)))
      val newOutput     = currentOutput ++ update(x).filterNot(_ == Cop1(x))
      update - x + (outputVar -> newOutput)
    }

    // 文字で微分することを試みるが、文字を消費しなかったら、e0 に戻ってマッチを再開する。
    // JS の replaceAll 関数においては、一文字もマッチしていないときに空文字列にマッチした場合、
    // 一文字あとからマッチを再開しなければならない。例えば、"aa".replaceAll(/.*?/, "($&)") === "()a()a()".
    def deriveOrRestart(a: A)(e: Reg): Seq[(Reg, UpdateY)] = derive(a)(e) flatMap {
      // a を消費できたら、そのまま継続する
      case (Some(ee), update) => Seq((ee, simulateWithOutVar(update)))
      case (None, update)     =>
        // 新たなマッチを探す前に、現在の値で repl を outputVar に追加して、他の変数はリセットする
        val newOutput    = (Update.identity(sstVars) ++ update).subst(repl)
        val appendOutput = Update.reset(sstVars) + (outputVar -> (Cop1(outputVar) +: newOutput))

        // e0 に空文字列をマッチさせたなら、次に読む文字から e0 へのマッチを再開する
        // それ以外に空文字列をマッチさせたなら、今読んだ文字 a から新たなマッチを模倣する
        val transitionsByA: Seq[(Reg, UpdateY)] =
          if (e == e0) Seq((e0, Map(outputVar -> (List(Cop1(outputVar), Cop2(a))))))
          else deriveOrRestart(a)(e0)

        // 以上の 2 動作をワンステップで実行する
        transitionsByA map { case (eee, update1) =>
          val initialUpdate = Update.identity(sstVars) ++ simulateWithOutVar(update1)
          val update2       = Monoid[UpdateY].combine(appendOutput, initialUpdate)
          (eee, update2)
        }
    }

    // 遷移の集合
    def nextStates(q: Q, a: A): Set[(Q, Update[Y, A])] = {
      val lowest      = q.last
      val highers     = q.init
      val nextHighers = (highers >>= (deriveOrRestart(a))).map(_._1).distinct
      val nextLower   = deriveOrRestart(a)(lowest).distinctBy(_._1)
      var nexts       = Set.empty[(Q, Update[Y, A])]
      for (n <- 1 to nextLower.length if !nextHighers.contains(nextLower(n - 1)._1)) {
        val lowerExps = nextLower.take(n).map(_._1)
        val nextExps  = nextHighers ++ lowerExps
        val nextQ     = NonEmptyNub(nextExps.head, nextExps.tail)
        val update    = Update.identity(sstVars) ++ nextLower(n - 1)._2
        nexts += ((nextQ, update))
      }
      nexts
    }
    val (states, edges) = searchStates(Set(q0), alphabet)(nextStates)(
      { case (r, _) => r },
      { case (q, a, (r, w)) => (q, a, w, r) }
    )

    // 出力関数

    // "エンドマーカーによる微分"。
    // ターゲット正規表現が空文字列にマッチする場合は、最後にもう一度マッチするので2回微分することになる。
    def deriveEpsTwice(e1: Reg): Option[Cupstar[Y, A]] =
      deriveEps(e1).headOption.map { update =>
        if (update.isDefinedAt(botVar)) Nil
        else if (e1 == e0 || deriveEps(e).isEmpty) (Update.identity(sstVars) ++ update).subst(repl)
        else (Update.identity(sstVars) ++ update).subst(repl) ++ Update.reset(sstVars).subst(repl)
      }

    val outGraph = for {
      q          <- states if q.init.forall(deriveEps(_).isEmpty)
      lastOutput <- deriveEpsTwice(q.last).headOption
    } yield q -> (Cop1(outputVar) +: lastOutput)

    // copyless にする。
    // outputVar 以外の変数 x の右辺には、x 以外の変数が出現しない。
    type Z = Either[Int, (X, Int)]
    implicit def convertOutputVar(y: Y): Z = {
      require(y == outputVar)
      Left(outputVar.swap.toOption.get)
    }
    val refCnt: Map[X, Int] = replacement.foldLeft(e.groupVars.map(_ -> 0).toMap) {
      case (m, Cop1(x)) => m + (x -> (m(x) + 1))
      case (m, Cop2(a)) => m
    }
    val zs: Set[Z] = sstVars flatMap {
      case Right(x) => for (i <- 0 until refCnt(x)) yield Right((x, i))
      case Left(i)  => Seq(Left(i))
    }

    // 例えば a x b x c を a (x, 0) b (x, 1) c
    def copylessS(string: Cupstar[Y, A]): Cupstar[Z, A] = {
      var cnt = refCnt
      string.reverse
        .map[Cop[Z, A]] {
          case Cop2(a)           => Cop2(a)
          case Cop1(`outputVar`) => Cop1(outputVar)
          case Cop1(Right(x)) =>
            cnt = cnt.updated(x, cnt(x) - 1)
            Cop1(Right((x, cnt(x))))
          case _ => throw new Exception("copylessS: invalid string: " + string)
        }
        .reverse
    }

    def copylessU(update: UpdateY): Update[Z, A] = update flatMap {
      case (Right(x) -> (Cop1(y) :: w)) =>
        assert(Right(x) == y, s"x: $x\ty: $y")
        assert(w.forall(_.is2))
        for (i <- 0 until refCnt(x)) yield {
          val xi = Right((x, i))
          xi -> (Cop1(xi) +: copylessS(w))
        }
      case (Right(x) -> w) =>
        assert(w.forall(_.is2))
        for (i <- 0 until refCnt(x)) yield {
          val xi = Right((x, i))
          xi -> copylessS(w)
        }
      case (`outputVar` -> w) => Seq((outputVar: Z) -> copylessS(w))
      case _                  => throw new Exception("copylessU: invalid update: " + update)
    }

    NSST(
      states,
      alphabet,
      zs,
      edges.map { case (q, a, m, r) => (q, a, copylessU(m), r) },
      q0,
      graphToMap(outGraph.map { case (q, w) => (q, copylessS(w)) })(identity)
    )
  }

  def toReplaceFirstSST[A, X](
      e: PCRE[A, X],
      alphabet: Set[A],
      replacement: Cupstar[X, A]
  ) = {
    type Y   = Option[X]
    type Reg = PCRE[A, Y]
    val suffixVar: Y = None
    val e0: Reg =
      PCRE.Cat(e.renameVars(Some.apply), PCRE.Group(PCRE.Greedy(PCRE.AllChar()), suffixVar))
    val repl: Cupstar[Y, A] = replacement.map {
      case Cop1(x) => Cop1(Some(x))
      case Cop2(b) => Cop2(b)
    } :+ Cop1(suffixVar)
    toReplaceAllSST(e0, alphabet, repl)
  }

}
