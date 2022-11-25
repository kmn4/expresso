package com.github.kmn4.expresso.machine

import org.scalatest.funsuite.AnyFunSuite

class DataStringTheory2Test extends AnyFunSuite {

  // テストする性質
  // 1. SDST のセマンティクス (合成の正しさ含む)
  // 2. 関数性と等価性

  // テストする機械
  // a. defop の SDST (DONE)
  // b. defprog の SDST (DONE)
  // c. liftDelim, delim_scheme (DONE)
  // d. 手書きされた機械 (TODO)

  val Defop   = DefopMachines
  val Defprog = DefprogMachines
  import SDSTSemantics._

  /// semantics tests

  // defop semantics
  test("defop take semantics") { SemanticsSpecs.take(Defop.take("n"), "n") }
  test("defop drop semantics") { SemanticsSpecs.drop(Defop.drop("n"), "n") }
  test("defop take-even semantics") { SemanticsSpecs.takeEven(Defop.takeEven) }
  test("defop reverse semantics") { SemanticsSpecs.reverse(Defop.reverse) }
  test("defop identity semantics") { SemanticsSpecs.identity(Defop.identity) }

  // defprog semantics
  def concatSplitSpec(machine: SimpleStreamingDataStringTransducer2, i: String) = {
    assert(transduce(machine, Map(i -> -2), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
    assert(transduce(machine, Map(i -> 2), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
    assert(transduce(machine, Map(i -> 5), seq(1, 2, 3, :#)) == seq(1, 2, 3, :#))
  }

  test("defprog concat-split sematics")(concatSplitSpec(Defprog.concatSplit, "n"))

  /// functionality and equivalence tests

  import DataStringTheory2.{checkEquivalence, checkFunctionality, compose}

  test("func? take") { assert(checkFunctionality(Defop.take("n"))) }
  test("func? drop") { assert(checkFunctionality(Defop.drop("n"))) }
  test("func? takeEven") { assert(checkFunctionality(Defop.takeEven)) }
  test("func? reverse") { assert(checkFunctionality(Defop.reverse)) }
  test("func? identity") { assert(checkFunctionality(Defop.identity)) }

  // defop equivalence
  test("!(equiv? take drop)") { assert(!checkEquivalence(Defop.take("n"), Defop.drop("n"))) }
  test("!(equiv? take identity)") { assert(!checkEquivalence(Defop.take("n"), Defop.identity)) }

  // defprog equivalence
  test("equiv? concat-split identity") { assert(checkEquivalence(Defprog.concatSplit, Defprog.identity)) }
  test("!(equiv? te-rev rev-te)") {
    assert(!checkEquivalence(Defprog.takeEven_reverse, Defprog.reverse_takeEven))
  }
  test("equiv? te-rev rev-te (assuming input length is odd)") {
    assert(
      Evaluator.checkEquiv(
        Defprog.takeEven_reverse,
        Defprog.reverse_takeEven,
        Reader.assumptions("(= (mod length 2) 1)")
      )
    )
  }
  test("equiv?! drop-reverse reverse-take") {
    assert(checkEquivalence(Defprog.dropReverse, Defprog.reverseTake))
  }
  test("!(equiv? drop-drop drop-sum)") { assert(!checkEquivalence(Defprog.dropDrop, Defprog.dropSum)) }
  test("equiv? drop-drop drop-sum (assuming n1, n2 >= 0)") {
    assert(Evaluator.checkEquiv(Defprog.dropDrop, Defprog.dropSum, Reader.assumptions("(>= n1 0) (>= n2 0)")))
  }
  test("equiv? take-all identity") { assert(checkEquivalence(Defprog.takeAll, Defprog.identity)) }

  /// tests for liftDelim, delim_scheme ...

  import SimpleStreamingDataStringTransducer2.{liftDelim, delim_scheme, concatDelim, projection}

  val concat = compose(concatDelim(2, Seq(0, 1)), projection(3, Seq(2)))
  //                   ^ w0#w1# => w0#w1#w0.w1#   ^ w0#w1#w2# => w2#

  def concatSpecs(machine: SimpleStreamingDataStringTransducer2) = {
    assert(checkFunctionality(machine))
    assert(transduce(machine, seq(1, 2, :#, 3, :#)) == seq(1, 2, 3, :#))
    assert(transduce(machine, seq(:#, 3, :#)) == seq(3, :#))
    assert(transduce(machine, seq(1, 2, :#, :#)) == seq(1, 2, :#))
    assert(transduce(machine, seq(:#, :#)) == seq(:#))
    assertThrows[OutputNotDefinedException] { transduce(machine, seq()) }
    assertThrows[OutputNotDefinedException] { transduce(machine, seq(:#)) }
    assertThrows[OutputNotDefinedException] { transduce(machine, seq(:#, :#, :#)) }
    assertThrows[OutputNotDefinedException] { transduce(machine, seq(:#, :#, 1)) }
  }
  test("concatDelim compose projection") { concatSpecs(concat) }

  val liftedIdentity = liftDelim(Defop.identity, 2, 0) // w0#w1# => w0#w1#w0#
  def liftedIdentitySpecs(machine: SimpleStreamingDataStringTransducer2) = {
    assert(checkFunctionality(machine))
    assert(transduce(machine, seq(1, :#, 2, :#)) == seq(1, :#, 2, :#, 1, :#))
    assert(transduce(machine, seq(:#, 2, :#)) == seq(:#, 2, :#, :#))
    assert(transduce(machine, seq(1, :#, :#)) == seq(1, :#, :#, 1, :#))
    assert(transduce(machine, seq(:#, :#)) == seq(:#, :#, :#))
    assertThrows[OutputNotDefinedException] { transduce(machine, seq(:#)) }
    assertThrows[OutputNotDefinedException] { transduce(machine, seq(:#, :#, :#)) }
    assertThrows[OutputNotDefinedException] { transduce(machine, seq(:#, :#, 1)) }
  }

  test("liftDelim defop identity") { liftedIdentitySpecs(liftedIdentity) }

  // counter: w0#w1#w2# => ε
  // lengthParam(i): wi の長さ
  val (counter, lengthParam) = delim_scheme(
    numReadStrings = 3,
    concatOperands = None,
    preserveList = _ => false,
    useLength = Set.from(0 until 3)
  )

  def counter3Specs(machine: SimpleStreamingDataStringTransducer2, param: Map[Int, String]) = {
    assert(checkFunctionality(machine))
    def shouldCount(fst: Int, snd: Int, thd: Int) =
      transduce(machine, Map(param(0) -> fst, param(1) -> snd, param(2) -> thd), _)
    assert(shouldCount(0, 1, 2)(seq(:#, 1, :#, 2, 3, :#)) == seq())
    assert(shouldCount(1, 0, 2)(seq(1, :#, :#, 2, 3, :#)) == seq())
    assert(shouldCount(1, 2, 0)(seq(1, :#, 2, 3, :#, :#)) == seq())
    assert(shouldCount(0, 0, 0)(seq(:#, :#, :#)) == seq())
    assertThrows[OutputNotDefinedException](shouldCount(0, 0, 0)(seq(1, :#, :#, :#)))
    assertThrows[OutputNotDefinedException](shouldCount(0, 0, 0)(seq(:#, :#, :#, 1)))
    assertThrows[OutputNotDefinedException](shouldCount(0, 0, 0)(seq(:#, :#, :#, :#)))
  }

  test("delim_scheme (counter)")(counter3Specs(counter, lengthParam))

}

extension [A](self: Reader.SListParser[A]) {
  def apply(code: String): A = ReaderRunner.read(self)(code).get
}
