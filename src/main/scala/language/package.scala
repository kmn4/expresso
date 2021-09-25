package com.github.kmn4.expresso

import com.github.kmn4.expresso.machine._

/**
  * 対象とする文字列制約の構文と，計算モデルへの変換方法を提供する．
  * 主なトレイトは以下の通り:
  *   - RegExp は順序を持たない正規表現
  *   - PCRE はマッチの優先順序とキャプチャグループをサポートする正規表現
  *   - ParikhTransduction は Parikh SST へと変換できる unary トランスダクション
  *   - ParikhLanguage は Parikh オートマトンへと変換できる言語
  *   - Constraint は代入文 (y = T(x)) や言語表明 (x \in L) の構文
  *     - ParikhAssignment は代入文
  *     - ParikhAssertion は言語表明
  *     - IntConstraint は線形算術論理式
  */
package object language {

  /** Construct DFA which accepts strings whose suffix is target.
    *  Each state i represents target.substring(0, i). */
   def postfixDFA[A](target: Seq[A], in: Set[A]): DFA[Int, A] = {
    require(target.length > 0)
    // KMP backtracking table (taken and adapted from Wikipedia)
    val table: Vector[Int] = if (target.length == 1) Vector(-1) else {
      // target.length >= 2
      var t = Vector(-1, 0)
      var i = 2
      var j = 0
      while (i < target.length) {
        if (target(i-1) == target(j)) {
          t = t.appended(j+1)
          i += 1
          j += 1
        } else if (j > 0) {
          j = t(j)
        } else {
          t = t.appended(0)
          i += 1
        }
      }
      t
    }
    val states = Set.from(0 to target.length)
    val q0 = 0
    val qf = target.length
    val delta = Map.from {
      for (q <- states; a <- in if q != qf)
        yield (q, a) -> {
          var j = q
          while (j >= 0 && a != target(j)) {
            j = table(j)
          }
          j + 1
        }
    }
    new DFA(
      states,
      in,
      delta,
      q0,
      Set(qf)
    )
  }

  def postfixDOT(target: String) = {
    import com.github.kmn4.expresso.machine.DOTMaker._
    val dot = postfixDFA(target, target.toSet).toDOT
    println(dot)
  }

}
