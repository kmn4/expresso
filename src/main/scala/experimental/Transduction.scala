package com.github.kmn4.sst.experimental

import com.github.kmn4.sst.ParikhSST
import com.github.kmn4.sst.NopLogger
import com.github.kmn4.sst.graphToMap
import com.github.kmn4.sst.Presburger
import com.github.kmn4.sst.Presburger.Sugar._

// A*(#1)...(#k-1)A*, n1, ..., nl -> A*
trait Transduction[A, B] {
  // pa の逆像を計算する
  // maxID がいまある最大の ID．
  // 新しく使う ID はこれよりも大きくする．
  def preImage[R, K](pa: ParikhAutomaton[R, B, K, String], maxID: Int): PreImage[Int, A, Int, String]
}

object Transduction {
  // psst の定義域は w_0 #_0 ... #_n-2 w_n-1 の形をした文字列の集合
  implicit class ParikhTransduction[Q, A, B, X, L](
      psst: ParikhSST[Q, Either[A, Int], B, X, L, String]
  ) extends Transduction[A, B] {

    // psst の定義域が w_0 #_0 ... #_n-2 w_n-1 のとき arity = n
    val arity = psst.inSet.flatMap(_.toOption).maxOption.getOrElse(-1) + 2

    override def preImage[R, K](
        lang: ParikhAutomaton[R, B, K, String],
        maxID: Int
    ): PreImage[Int, A, Int, String] = {
      // lang を PSST とみなす
      // PSST 同士の合成をする (LC-APSST まで)
      // 受理状態を固定するごとに1つの PA をつくる
      // PA を # で分割して PR にする

      // lang を PSST とみなす
      val langPST = {
        ParikhSST[R, B, Nothing, Nothing, K, String](
          lang.states,
          lang.inSet,
          Set.empty,
          lang.ls,
          lang.is,
          lang.edges.map { case (q, b, v, r) => (q, b, Map.empty, v, r) },
          lang.q0, {
            val (qf, v) = lang.acceptRelation
            Set((qf, Nil, v))
          },
          lang.acceptFormulas
        )
      }

      // PSST 同士の合成をする (LC-PA まで)
      val lcp = psst
        .composeNsstsToMsst[R, Nothing, Nothing, K](psst, langPST)(NopLogger)
        .toLocallyConstrainedAffineParikhSST
        .toLocallyConstrainedParikhSST
        .renamed
        .optimized

      // lcp を受理状態ごとに PA へ分割
      val pas: LazyList[ParikhAutomaton[Int, Either[A, Int], Int, String]] = {
        val qf = lcp.states.maxOption.getOrElse(0) + 1 // 存在しなかったら LazyList が空
        val states = lcp.states + qf
        val lastSharp = Right(arity - 1)
        val zero = lcp.ls.map(_ -> 0).toMap
        // TODO 到達性で状態を減らす
        // TODO 不要な L を削除
        LazyList.from(lcp.outGraph).map {
          case (q, _, v, phi) =>
            ParikhAutomaton(
              maxID, // この PA は一時的なものなので maxID を使ってもいい
              states,
              lcp.inSet + lastSharp,
              lcp.ls,
              lcp.is,
              lcp.edges.map { case (q, a, _, v, r) => (q, a, v, r) } + ((q, lastSharp, v, qf)),
              lcp.q0,
              (qf, zero),
              lcp.globalAcceptFormulas :+ phi // TODO phi は Seq のほうがいいかも?
            )
        }
      }

      def copyVar[L](paID: Int, l: L) = s"copy_${paID}_${l}"
      def sumVar[L](paID: Int, l: L) = s"sum_${paID}_${l}"

      def split[Q, L](
          pa: ParikhAutomaton[Q, Either[A, Int], L, String]
      ): LazyList[(Seq[ParikhAutomaton[Q, A, L, String]], Seq[Presburger.Formula[String]])] = {
        type Edge = (Q, Either[A, Int], Map[L, Int], Q)

        // cache
        val backTrans: Map[(Q, Either[A, Int]), Set[(Q, Map[L, Int])]] =
          graphToMap(pa.edges) { case (q, a, v, r) => (r, a) -> (q, v) }
        val trans: Map[(Q, Either[A, Int]), Set[(Q, Map[L, Int])]] =
          graphToMap(pa.edges) { case (q, a, v, r) => (q, a) -> (r, v) }

        // pa 上で qf から戻れないものを刈る
        def pruneStatesBack(qf: Q): (Set[Q], Set[Edge]) =
          com.github.kmn4.sst.searchStates(Set(qf), pa.inSet) {
            case (r, a) => backTrans((r, a))
          }(_._1, { case (r, a, (q, v)) => (q, a, v, r) })

        // pa 上で q0 から到達できないものを刈る
        def pruneStatesForward(q0: Q): (Set[Q], Set[Edge]) =
          com.github.kmn4.sst.searchStates(Set(q0), pa.inSet) {
            case (q, a) => trans((q, a))
          }(_._1, { case (q, a, (r, v)) => (q, a, v, r) })

        // pa 上で q0 から到達可能かつ qf から逆到達可能
        def pruneStates(q0: Q, qf: Q): (Set[Q], Set[Edge]) = {
          val (qs1, es1) = pruneStatesBack(qf)
          val (qs2, es2) = pruneStatesForward(q0)
          (qs1 intersect qs2, es1 intersect es2)
        }

        // pa の状態を qs, 辺集合を es に制限．
        // 状態が空なら None になる
        // NOTE id は呼び出し元で上書きすること
        // NOTE acceptRelation は呼び出し元で上書きすること
        def statesRemoved(
            qs: Set[Q],
            es: Set[Edge]
        ): Option[ParikhAutomaton[Q, Either[A, Int], L, String]] =
          if (qs.isEmpty) None
          else Some { pa.copy(states = qs, edges = es) } // id, acceptRelation はあとで上書きされる

        def prune(q0: Q, qf: Q): Option[ParikhAutomaton[Q, Either[A, Int], L, String]] = {
          val (qs, es) = pruneStates(q0, qf)
          statesRemoved(qs, es)
        }

        def pruneBackward(qf: Q): Option[ParikhAutomaton[Q, Either[A, Int], L, String]] = {
          val (qs, es) = pruneStatesBack(qf)
          statesRemoved(qs, es)
        }

        // sharp はないはず．あったら例外を投げる
        def mustRemoveSharps(
            pa: ParikhAutomaton[Q, Either[A, Int], L, String]
        ): ParikhAutomaton[Q, A, L, String] = {
          pa.copy(
            inSet = pa.inSet.flatMap(_.left.toOption),
            edges = pa.edges.map(e => e.copy(_2 = e._2.left.toOption.get))
          )
        }

        def splitAux(
            pa: ParikhAutomaton[Q, Either[A, Int], L, String],
            i: Int
        ): LazyList[(Seq[ParikhAutomaton[Q, A, L, String]], Seq[Presburger.Formula[String]])] = {
          val sharpEdge: Map[Int, Iterable[Edge]] = graphToMap(pa.edges.filter(_._2.isRight)) {
            case e @ (_, Right(i), _, _) => i -> e
            case _                       => throw new Exception("This cannot be the case.")
          }

          val newID = maxID + i + 1

          if (i == 0) {
            for {
              sharp0 @ (q0, _, v, _) <- LazyList.from(sharpEdge(0))
              pa0 <- pruneBackward(q0)
            } yield {
              import Presburger._
              val noSharp = mustRemoveSharps(pa0)
              val syncFormulas = // PA と大域整数制約の同期
                pa0.ls.toSeq.map(l => Eq[Either[String, L]](Var(Right(l)), Var(Left(sumVar(newID, l)))))
              val newPA = noSharp.copy(
                id = newID,
                acceptRelation = (q0, v),
                acceptFormulas = syncFormulas
              )
              (Seq(newPA), Seq.empty)
            }
          } else if (i > 0) {
            for {
              sharp1 @ (q1, _, _, r1) <- LazyList.from(sharpEdge(i - 1))
              sharpI @ (qi, _, v, _) <- sharpEdge(i)
              paI <- prune(r1, qi).toList
              pa1 <- pruneBackward(q1).map { pa =>
                // 再帰のため最後に #_i-1 で遷移するようにしたい
                // TODO もう少し綺麗に書けるのでは
                //      例えば PA は # 終端しない文字列組を受理することにする
                pa.copy(
                  states = pa.states + r1,
                  edges = pa.edges + sharp1
                )
              }.toList
              (relation1, formula) <- splitAux(pa1, i - 1)
            } yield {
              import Presburger._
              val noSharp = mustRemoveSharps(paI)
              // l (L) === copy_id_l (I)
              val copyFormulas =
                paI.ls.toSeq.map(l => Eq[Either[String, L]](Var(Right(l)), Var(Left(copyVar(newID, l)))))
              // sum_id_l === sum_{id-1}_l + copy_id_l
              val syncFormulas = paI.ls.map { l =>
                val sumL = Var(sumVar(newID, l))
                val prevL = Var(sumVar(newID - 1, l))
                val copyL = Var(copyVar(newID, l))
                Eq(sumL, Add(Seq(prevL, copyL)))
              }
              val newPA = noSharp.copy(
                id = newID,
                acceptRelation = (qi, v),
                acceptFormulas = copyFormulas
              )
              (Seq(newPA), Seq.empty)
              (relation1 :+ newPA, formula ++ syncFormulas)
            }
          } else throw new Exception("i < 0")
        }

        splitAux(pa, arity - 1)
      }

      for {
        pa <- pas
        (rel, phi) <- split(pa)
      } yield (
        rel,
        phi ++ pa.acceptFormulas.map(_.renameVars {
          case Right(l) => sumVar(maxID + arity, l)
          case Left(i)  => i
        })
      )
    }

  }

}
