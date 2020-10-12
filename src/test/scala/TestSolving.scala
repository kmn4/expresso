package com.github.kmn4.sst

import org.scalatest.flatspec._

class TestSolving extends AnyFlatSpec {
  def cupstarOf(xs: Set[Char], s: String): Concepts.Cupstar[Char, Char] =
    s.map(c => if (xs contains c) Cop1(c) else Cop2(c)).toList
  def updateOf(
      xs: Set[Char],
      m: Map[Char, String]
  ): Concepts.Update[Char, Char] =
    xs.map(x => x -> cupstarOf(xs, m.getOrElse(x, x.toString()))).toMap
  def createNSST(
      states: Set[Int],
      in: Set[Char],
      xs: Set[Char],
      edges: List[(Int, Char, Int, Map[Char, String])],
      q0: Int,
      f: Map[Int, Set[String]]
  ) = new NSST(
    states,
    in,
    xs,
    edges.map { case (q, a, r, m) => (q, a, updateOf(xs, m), r) }.toSet,
    q0,
    f.view.mapValues(_.map(cupstarOf(xs, _))).toMap
  )
  "Zhu's experiment case 1" should "be sat" in {
    val s1 = createNSST(
      Set(0, 1),
      Set('a', 'b', '#'),
      Set('0', '1'),
      List(
        (0, 'a', 0, Map('0' -> "0a", '1' -> "1b")),
        (0, 'b', 0, Map('0' -> "0b", '1' -> "1b")),
        (0, '#', 1, Map.empty)
      ),
      0,
      Map(1 -> Set("0#1#"))
    )
    val s2 = createNSST(
      Set(0, 1, 2),
      Set('a', 'b', '#'),
      Set('0', '1', '2'),
      List(
        (0, 'a', 0, Map('0' -> "0a")),
        (0, 'b', 0, Map('0' -> "0b")),
        (0, '#', 1, Map.empty),
        (1, 'a', 1, Map('1' -> "1a", '2' -> "2a")),
        (1, 'b', 1, Map('1' -> "1b", '2' -> "2b")),
        (1, '#', 2, Map('2' -> "a2a"))
      ),
      0,
      Map(2 -> Set("0#1#2#"))
    )
    val s3 = createNSST(
      Set(0, 1, 2, 3, 4, 5),
      Set('a', 'b', '#'),
      Set('0', '1', '2'),
      List(
        (0, 'a', 0, Map('0' -> "0a")),
        (0, 'b', 0, Map('0' -> "0b")),
        (0, '#', 1, Map.empty),
        (1, 'a', 1, Map('1' -> "1a")),
        (1, 'b', 1, Map('1' -> "1b")),
        (1, '#', 2, Map.empty),
        (2, 'a', 3, Map('2' -> "2a")),
        (3, 'b', 3, Map('2' -> "2b")),
        (3, 'a', 4, Map('2' -> "2a")),
        (4, '#', 5, Map.empty)
      ),
      0,
      Map(5 -> Set("0#1#2#"))
    )
    // (s3 s2) s1, rather than s3 (s2 s1)
    val start = System.nanoTime()
    val t1 = NSST.composeNsstsToNsst(s2, s3)
    val t2 = NSST.composeNsstsToNsst(s1, t1)
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${t2.states.size}")
    info(s"variables:\t${t2.variables.size}")
    info(s"transition:\t${t2.edges.size}")
    assert(t2.transduce("aba#".toList) == Set("aba#bbb#abbba#".toList))
    info(s"witness: ${t2.takeInput}")
    info(s"output: ${t2.transduce(t2.takeInput)}")
  }

  // Construct DFA which accepts strings whose postfix is target.
  // Each state i represents target.substring(0, i).
  private def postfixDFA(target: String, in: Set[Char]) = {
    // KMP backtracking table
    val table: Vector[Int] = {
      var t = Vector(-1)
      for (i <- 1 until target.length) {
        val prev = t(i - 1)
        t = t.appended(prev + (if (target(i - 1) == target(prev + 1)) 1 else 0))
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
  // Returns update which appends `w` to variable `x`, and is identity on other variables in `xs`.
  def appendWordTo[X, A](x: X, xs: Set[X], w: List[A]): Concepts.Update[X, A] =
    xs.map(y => y -> (List(Cop1(y)) ++ (if (y == x) w.map(Cop2(_)) else Nil))).toMap
  // Returns `alphabet` to `alphabet` NSST whose state set is {0, ... n} and variable set is {0, 1}.
  // On each state i the NSST appends input character to variable 0.
  // It transitions to next state when it reads `None`, appending `None` to variable 0.
  // Its output function value is `0 None 1 None` on state n, and empty on other ones.
  // So the NSST reads string of the form "w0 None w1 None ... w(n-1) None" and
  // outputs "w0 None w1 None ... w(n-1) None None" (because it doesn't append any char to var 1).
  def solverNsstTemplate(
      n: Int,
      alphabet: Set[Char]
  ): NSST[Int, Option[Char], Option[Char], Int] = {
    type Q = Int
    type X = Int
    type A = Option[Char]
    type B = Option[Char]
    val states = Set.from(0 to n)
    val xs = Set(0, 1)
    val q0 = 0
    val outF: Map[Q, Set[Concepts.Cupstar[X, B]]] = Map(
      n -> Set(List(Cop1(0), Cop1(1), Cop2(None)))
    )
    val updates = Concepts.updateMonoid(xs)
    type Edges = Set[(Q, A, Concepts.Update[X, B], Q)]
    val edges: Edges = {
      val appendingEdges: Edges =
        for (i <- states; a <- alphabet if i != n)
          yield (i, Some(a), updates.unit + (0 -> List(Cop1(0), Cop2(Some(a)))), i)
      val toNextEdges: Edges =
        for (i <- states; if i != n)
          yield (i, None, updates.unit + (0 -> List(Cop1(0), Cop2(None))), i + 1)
      appendingEdges ++ toNextEdges
    }
    new NSST(
      states,
      (alphabet.map[Option[Char]](Some(_))) + None,
      xs,
      edges,
      q0,
      outF
    )
  }
  // Returns NSST whose states `q`s are embedded to Cop2(q).
  def embedStates2[P, Q, A, B, X](n: NSST[Q, A, B, X]): NSST[Cop[P, Q], A, B, X] = {
    new NSST(
      n.states.map(Cop2(_)),
      n.in,
      n.variables,
      n.edges.map { case (q, a, m, r) => (Cop2(q), a, m, Cop2(r)) },
      Cop2(n.q0),
      n.partialF.map { case (q, s) => Cop2(q) -> s }
    )
  }
  // Construct NSST which replaces `target` in `j`-th input string with `word`,
  // and output it as `i`-th string.
  def replaceAllNSST(
      target: String,
      word: String,
      i: Int,
      j: Int,
      in: Set[Char]
  ): NSST[Int, Option[Char], Option[Char], Int] = {
    if (i <= j) {
      throw new Exception()
    }
    // States of the form Cop1(q) are the states of j-th component.
    type Q = Cop[Int, Int]
    type X = Int
    type A = Option[Char]
    type B = Option[Char]
    type Update = Concepts.Update[X, B]
    val base: NSST[Q, A, B, X] = embedStates2(solverNsstTemplate(i, in))
    val xs = base.variables
    val updates: Monoid[Update] = Concepts.updateMonoid(xs)
    val dfa = postfixDFA(target, in)
    type Edges = Set[(Q, A, Update, Q)]
    val edges: Edges = {
      val notFromJ: Edges = {
        val baseEdges = base.edges.filter {
          case (q, a, _, _) => q != Cop2(j) && !(q == Cop2(j - 1) && a == None)
        }
        // On state j-1, machine should transition to Cop1(q0) by reading None.
        baseEdges + (
          (
            Cop2(j - 1),
            None,
            updates.unit + (0 -> List(Cop1(0), Cop2(None))),
            Cop1(dfa.q0)
          )
        )
      }
      val jthComponent: Edges = {
        val states = dfa.states -- dfa.finalStates
        // On each state q, DFA has partially matched prefix of target string.
        // If translated SST reads None, it should append the stored string to variable i.
        val toNext: Edges =
          states.map(q => {
            val stored = target.substring(0, q)
            val appendStored = {
              Map(
                0 -> List(Cop1(0), Cop2(None)),
                1 -> (List(Cop1(1)) ++ stored.toList.map(a => Cop2(Some(a))))
              )
            }
            (Cop1(q), None, appendStored, Cop2(j + 1))
          })
        // In each transition, DFA discards some prefix string (possibly empty one).
        // SST should store it in variable 1 (it should also store input char in 0, of course).
        val edgesFromDfa: Edges = {
          for (q <- states; a <- in)
            yield {
              val t = dfa.transition((q, a))
              val (r, append) =
                if (dfa.finalStates contains t) {
                  (
                    dfa.q0,
                    word.toList.map(Some(_))
                  )
                } else {
                  val qStored = target.substring(0, q) + a
                  (
                    t,
                    qStored.substring(0, qStored.length - t).toList.map(Some(_))
                  )
                }
              val m = updates.combine(
                appendWordTo(0, xs, List(Some(a))),
                appendWordTo(
                  1,
                  xs,
                  append
                )
              )
              (Cop1(q), Some(a), m, Cop1(r))
            }
        }
        edgesFromDfa ++ toNext
      }
      (notFromJ ++ jthComponent)
    }
    val states = edges.map { case (q, _, _, _) => q } + Cop2(i)
    val q0 = if (j == 0) Cop1(dfa.q0) else Cop2(0)
    new NSST[Q, A, B, X](
      states,
      in.map(Some(_): Option[Char]) + None,
      xs,
      edges,
      q0,
      base.partialF
    ).renamed
  }
  // Construct NSST which output concatenation of `j`-th and `k`-th input in this order.
  def concatNSST(
      i: Int,
      j: Int,
      k: Int,
      alphabet: Set[Char]
  ): NSST[Int, Option[Char], Option[Char], Int] = {
    type Q = Int
    type A = Option[Char]
    type B = Option[Char]
    trait X
    trait Y extends X
    case object Input extends X
    case object J extends Y
    case object K extends Y
    // Almost same code as solverNsstTemplate, but here variable set has two addtional ones.
    val states = Set.from(0 to i)
    val xs: Set[X] = Set(Input, J, K)
    val q0 = 0
    val outF: Map[Q, Set[Concepts.Cupstar[X, B]]] =
      Map(i -> Set(List(Cop1(Input), Cop1(J), Cop1(K), Cop2(None))))
    val updates = Concepts.updateMonoid(xs)
    type Edges = Set[(Q, A, Concepts.Update[X, B], Q)]
    val edges: Edges = {
      // On states j (resp. k), append an char also to J (resp. K)
      val appendingEdges: Edges =
        for (q <- states; a <- alphabet if q != i)
          yield {
            val m = updates.unit + (Input -> List(Cop1(Input), Cop2(Some(a)))) ++
              (if (q == j) { Some((J -> List(Cop1(J), Cop2(Some(a))))) }
               else { None }) ++
              (if (q == k) { Some((K -> List(Cop1(K), Cop2(Some(a))))) }
               else { None })
            (q, Some(a), m, q)
          }
      // On state i-1, assign concat of j' and k' into i, and clear them.
      val toNextEdges: Edges =
        for (q <- states; if q != i)
          yield {
            val m = updates.unit + (Input -> List(Cop1(Input), Cop2(None)))
            (q, None, m, q + 1)
          }
      appendingEdges ++ toNextEdges
    }
    new NSST[Q, A, B, X](
      states,
      alphabet.map[Option[Char]](Some.apply) + None,
      xs,
      edges,
      q0,
      outF
    ).renamed
  }
  // Construct NSST which outputs exactly the same string as input,
  // if it is consist of `n` strings and its `i`-th (starting from 0) one
  // is in language represented by `re`.
  def regexNSST(
      n: Int,
      i: Int,
      re: RegExp[Char],
      alphabet: Set[Char]
  ): NSST[Int, Option[Char], Option[Char], Int] = {
    type DQ = Int
    val dfa: DFA[DQ, Char] = new RegExp2NFA(re).construct().toDFA.minimized
    type Q = Cop[DQ, Int]
    type A = Option[Char]
    type B = Option[Char]
    type X = Unit

    val base: NSST[Q, A, B, X] = {
      val states = Set.from(0 to n) - i
      val xs = Set(())
      val q0 = 0
      val outF: Map[Int, Set[Concepts.Cupstar[X, B]]] = Map(n -> Set(List(Cop1(()))))
      val updates = Concepts.updateMonoid(xs)
      type Edges = Set[(Int, A, Concepts.Update[X, B], Int)]
      val edges: Edges = {
        val appendingEdges: Edges =
          for (j <- states; a <- alphabet if j != n && j != i)
            yield (j, Some(a), updates.unit + (() -> List(Cop1(()), Cop2(Some(a)))), j)
        val toNextEdges: Edges =
          for (j <- states; if j != n && j + 1 != i)
            yield (j, None, updates.unit + (() -> List(Cop1(()), Cop2(None))), j + 1)
        appendingEdges ++ toNextEdges
      }
      embedStates2(
        new NSST(
          states,
          (alphabet.map[Option[Char]](Some(_))) + None,
          xs,
          edges,
          q0,
          outF
        )
      )
    }

    type Update = Concepts.Update[X, B]
    type Edge = (Q, A, Update, Q)
    type Edges = Set[Edge]
    // Replace state i with states of DFA.
    val states = base.states - Cop2(i) ++ dfa.states.map(Cop1.apply)
    val updates = Concepts.updateMonoid(base.variables)
    val edges: Edges = {
      base.edges +
        ((Cop2(i - 1), None, updates.unit + (() -> List(Cop1(()), Cop2(None))), Cop1(dfa.q0))) ++
        dfa.finalStates.map[Edge](q =>
          (Cop1(q), None, updates.unit + (() -> List(Cop1(()), Cop2(None))), Cop2(i + 1))
        ) ++
        dfa.transition.map[Edge] {
          case ((q, a), r) => {
            val m = updates.unit + (() -> List(Cop1(()), Cop2(Some(a))))
            (Cop1(q), Some(a), m, Cop1(r))
          }
        }
    }
    val q0 = if (i == 0) Cop1(dfa.q0) else Cop2(0)
    new NSST[Q, A, B, X](
      states,
      base.in,
      base.variables,
      edges,
      q0,
      base.partialF
    ).renamed
  } // End of regexNSST
  /** Returns NSST which transduces a string of form "w0 None ... w(n-1) None" to
    * "w'0 ... w'(n-1)" where each length of w'i is equal to that of wi and
    * each w'i is made up of only one integer i, which is distinct from other w'j.
    */
  def parikhNSST(n: Int, alpha: Set[Char]): NSST[Int, Option[Char], Int, Int] = {
    val states = Set.from(0 to n)
    type Q = Int
    type A = Option[Char]
    type B = Int
    type X = Int
    type Update = Concepts.Update[X, B]
    type Edge = (Q, A, Update, Q)
    val edges: Iterable[Edge] = {
      val loop: Iterable[Edge] =
        for (q <- 0 until n; a <- alpha)
          yield (q, Some(a), Map(0 -> List(Cop1(0), Cop2(q))), q)
      val next: Iterable[Edge] =
        for (q <- 0 until n) yield ((q, None, Map(0 -> List(Cop1(0))), q + 1))
      loop ++ next
    }
    new NSST(
      states,
      alpha.map[Option[Char]](Some.apply) + None,
      Set(0),
      edges.toSet,
      0,
      Map(n -> Set(List(Cop1(0))))
    )
  }
  def toOptionList(s: String): List[Option[Char]] =
    s.toList.map(c => if (c == '#') None else Some(c))
  def fromOptionList(l: List[Option[Char]]): String = l.map(_.getOrElse('#')).mkString
  "Zhu's experiment case 2" should "be sat" in {
    val p = postfixDFA("aab", Set('a', 'b', 'c'))
    assert(p.accept("aaab".toList))
    assert(!p.accept("abab".toList))
    assert(!p.accept("ababaaba".toList))
    val aab = replaceAllNSST("aab", "b", 1, 0, "ab".toSet)
    assert(aab.transduce(toOptionList("aaab#")) == Set(toOptionList("aaab#ab#")))
    assert(aab.transduce(toOptionList("aaaa#")) == Set(toOptionList("aaaa#aaaa#")))
    assert(aab.transduce(toOptionList("aabaab#")) == Set(toOptionList("aabaab#bb#")))
    val aab31 = replaceAllNSST("aab", "b", 3, 1, "ab".toSet)
    assert(aab31.transduce(toOptionList("#aab##")) == Set(toOptionList("#aab##b#")))

    val in = "<sc>".toSet
    val sc10 = replaceAllNSST("<sc>", "", 1, 0, in)
    assert(sc10.transduce(toOptionList("<sc>#")) == Set(toOptionList("<sc>##")))
    assert(sc10.transduce(toOptionList("<sc#")) == Set(toOptionList("<sc#<sc#")))
    val exp = CatExp(CatExp(CatExp(CharExp('<'), CharExp('s')), CharExp('c')), CharExp('>'))
    val sc = regexNSST(2, 1, exp, in)
    assert(sc.transduce(toOptionList("#<sc>#")) == Set(toOptionList("#<sc>#")))
    assert(sc.transduce(toOptionList("#<sc#")) == Set())
    val start = System.nanoTime()
    val composed = sc10 compose sc
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${composed.states.size}")
    info(s"variables:\t${composed.variables.size}")
    info(s"transition:\t${composed.edges.size}")
    assert(!composed.isEmpty)
    assert(composed.transduce(toOptionList("<sc<sc>>#")) == Set(toOptionList("<sc<sc>>#<sc>#")))
    info(s"witness: ${fromOptionList(composed.takeInput)}")
  }

  def compositionRight[Q, A, X](l: Seq[NSST[Q, A, A, X]]): NSST[Int, A, A, Int] = {
    l.map(_.renamed).reduceRight(NSST.composeNsstsToNsst(_, _).removeRedundantVars)
  }

  def testTransduce[Q, X](
      sst: NSST[Q, Option[Char], Option[Char], X],
      w: String,
      expected: String*
  ) = {
    assert(sst.transduce(toOptionList(w)) == expected.map(toOptionList).toSet)
  }

  "Zhu's experiment case 3" should "be sat" in {
    val in = "a<sc>".toSet
    val sc20 = replaceAllNSST("<sc>", "a", 2, 0, in)
    testTransduce(sc20, "a<s#c>a#", "a<s#c>a#a<s#")
    val sc31 = replaceAllNSST("<sc>", "a", 3, 1, in)
    testTransduce(sc31, "a<s#c>a#a<s#", "a<s#c>a#a<s#c>a#")
    val concat23 = concatNSST(4, 2, 3, in)
    testTransduce(concat23, "a<s#c>a#a<s#c>a#", "a<s#c>a#a<s#c>a#a<sc>a#")
    val re: RegExp[Char] = "a<sc>a".foldLeft[RegExp[Char]](EpsExp) {
      case (acc, c) => CatExp(acc, CharExp(c))
    }
    val reSST = regexNSST(5, 4, re, in)
    assert(reSST.transduce(toOptionList("####a<sc>a#")) == Set(toOptionList("####a<sc>a#")))
    assert(reSST.transduce(toOptionList("####a<sc>#")) == Set())
    testTransduce(reSST, "a<s#c>a#a<s#c>a#a<sc>a#", "a<s#c>a#a<s#c>a#a<sc>a#")
    val start = System.nanoTime()
    // sc20 -> sc31 -> concat -> reSST
    val composed = compositionRight(List(sc20, sc31, concat23, reSST))
    info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
    info(s"states:\t${composed.states.size}")
    info(s"variables:\t${composed.variables.size}")
    info(s"transition:\t${composed.edges.size}")
    testTransduce(composed, "a<s#c>a#", "a<s#c>a#a<s#c>a#a<sc>a#")
    assert(!composed.isEmpty)
    val witness = composed.takeInput
    info(fromOptionList(witness))
    assert(composed.transduce(witness) != Set.empty)
  }

  "Zhu's experiment case 5" should "be unsat" in {
    val in = Set('a', 'b')
    def cat(n: Int) = concatNSST(n + 1, n, n, in)
    val re1 = {
      val ab = CatExp(CharExp('a'), CharExp('b'))
      regexNSST(2, 1, CatExp(ab, StarExp(ab)), in)
    }
    def re(k: Int) = {
      val aa = CatExp(CharExp('a'), CharExp('a'))
      regexNSST(k + 1, k, CatExp(aa, StarExp(aa)), in)
    }
    def test(k: Int) = {
      val start = System.nanoTime()
      val composed = compositionRight((Seq(cat(0), re1) ++ (1 until k).map(cat) ++ Seq(re(k))))
      assert(composed.isEmpty)
      info(s"[k=$k]")
      info(s"elapsed:\t${(System.nanoTime() - start) / 1000000} ms")
      info(s"states:\t${composed.states.size}")
      info(s"variables:\t${composed.variables.size}")
      info(s"transition:\t${composed.edges.size}")
    }
    testTransduce(cat(1), "a#b#", "a#b#bb#")
    testTransduce(re1, "a#ab#", "a#ab#")
    testTransduce(re1, "a##")
    test(2)
    test(3)
    test(4)
    test(5)
  }

  "Variant of Zhu's benchmark int3" should "be sat" in {
    val alpha = "abc".toSet
    val s1 = replaceAllNSST("ab", "c", 1, 0, alpha)
    val s2 = replaceAllNSST("ac", "aaaa", 2, 1, alpha)
    val parikh = parikhNSST(3, alpha)
    val start = System.nanoTime()
    def elapsedMillis(): Long = (System.nanoTime() - start) / 1000000
    def printTime(s: String) = {
      info(s)
      info(s"elapsed:\t${elapsedMillis()} ms")
    }
    val composed = s1 compose s2
    printTime("composed")
    info(s"states: ${composed.states.size}")
    info(s"edges: ${composed.edges.size}")

    val parikhComposed = s1 compose (s2 compose parikh)
    printTime("prikhComposed")
    info(s"states:\t${parikhComposed.states.size}")
    info(s"edges:\t${parikhComposed.edges.size}")
    info(s"variables:\t${parikhComposed.variables.size}")

    assert(!composed.isEmpty)
    printTime("composed is not empty")

    val formula = parikhComposed.presburgerFormula
    printTime("Formula computed")

    import com.microsoft.z3
    val cfg = new java.util.HashMap[String, String]()
    cfg.put("model", "true")
    val ctx = new z3.Context(cfg)
    val freeVars = (0 until 3).map(i => s"y$i").map(y => y -> ctx.mkIntConst(y))
    val zero = ctx.mkInt(0)
    val positives = freeVars.map { case (_, v) => ctx.mkGe(v, zero) }
    val expr = Parikh.Formula.formulaToExpr(ctx, freeVars.toMap, formula)
    val growsOne = ctx.mkEq(ctx.mkSub(freeVars(2)._2, freeVars(0)._2), ctx.mkInt(1))
    val leThree = ctx.mkLe(freeVars(0)._2, ctx.mkInt(3))
    val solver = ctx.mkSolver()
    solver.add(expr +: leThree +: growsOne +: positives: _*)
    assert(solver.check() == z3.Status.SATISFIABLE)
    val m = solver.getModel()
    val witnessImage = ((0 until 3) zip freeVars).map {
      case (x, (_, i)) => x -> m.eval(i, false).toString.toInt
    }.toMap
    printTime("Z3 done")
    info(s"Image of witness:\t$witnessImage")

    val enft = NSST.convertNsstParikhNft(parikhComposed).toENFT
    printTime("Start to search for witness")
    val witness =
      enft.takeInputFor(witnessImage, m => m.exists { case (a, i) => i > witnessImage(a) })
    printTime("Got witness")
    info(s"witness: ${fromOptionList(witness)}") // => "aab#"
  }
}
