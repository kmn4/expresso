package com.github.kmn4.expresso

import com.typesafe.scalalogging.Logger
import org.scalactic.source.Position
import org.scalatest.funsuite._
import com.github.kmn4.expresso.strategy.Strategy
import com.github.kmn4.expresso.strategy.JSSST2021Strategy
import com.github.kmn4.expresso.strategy.PreImageStrategy

class ParikhSolverTest extends AnyFunSuite {
  val strategySpecs = Seq(
    ("jssst", new JSSST2021Strategy(_)),
    ("preimage", new PreImageStrategy(_))
  )

  for ((name, constr) <- strategySpecs) {
    runTests(name, constr)
  }

  def runTests(strategyName: String, strategyConstructor: Logger => Strategy) = {

    def withScript[T](reader: java.io.Reader)(body: smtlib.trees.Commands.Script => T): T = {
      val lexer = new smtlib.lexer.Lexer(reader)
      val parser = new smtlib.parser.Parser(lexer)
      val script = parser.parseScript
      body(script)
    }
    def withExecuteScript[T](strategy: Strategy, print: Boolean, logger: Logger, alphabet: Set[Char])(
        reader: java.io.Reader
    )(body: Solver => T): T = withScript(reader) { script =>
      val solver = new Solver(checker = strategy, print = print, logger = logger, alphabet = alphabet)
      solver.executeScript(script)
      body(solver)
    }
    def withExecuteScriptNoPrint[T](reader: java.io.Reader)(body: Solver => T): T = {

      val logger = Logger("nop")
      val strategy = strategyConstructor(logger)
      withExecuteScript(strategy, false, logger = logger, "ab".toSet)(reader)(body)
    }
    def testWithInfoTime[T](testName: String, testTags: org.scalatest.Tag*)(
        testFun: => Any
    )(implicit pos: Position): Unit = test(testName, testTags: _*) {
      val started = System.nanoTime()
      testFun
      val finished = System.nanoTime()
      info(s"Took ${(finished - started) / 1000000} ms")
    }
    // TODO assertions の自動導出
    def testSAT(
        constraint: String
    )(assertions: (Map[String, String], Map[String, Int]) => Unit)(implicit pos: Position) =
      testWithInfoTime(s"[$strategyName] test SAT\n${constraint.trim}") {
        withExecuteScriptNoPrint(new java.io.StringReader(constraint)) { solver =>
          solver.getModel() match {
            case Some((sModel, iModel)) => assertions(sModel, iModel)
            case None                   => fail()
          }
        }
      }
    def testUNSAT(constraint: String)(implicit pos: Position) =
      testWithInfoTime(s"[$strategyName] test UNSAT\n${constraint.trim}") {
        withExecuteScriptNoPrint(new java.io.StringReader(constraint)) { solver =>
          assert(solver.getModel().isEmpty)
        }
      }

    def withFileReader[T](fname: String)(body: java.io.FileReader => T): T = {
      val path = java.nio.file.FileSystems.getDefault().getPath(fname)
      val reader = new java.io.FileReader(path.toFile())
      try {
        body(reader)
      } finally {
        reader.close()
      }
    }

    def withExecuteFile[T](fname: String)(body: Solver => T): T =
      withFileReader(s"constraints/bench/$fname.smt2") { reader =>
        val logger = Logger(s"bench.$strategyName.$fname")
        val strategy = strategyConstructor(logger)
        withExecuteScript(strategy, false, logger, "ab".toSet)(reader)(body)
      }

    def testFileSAT(
        name: String
    )(assertions: (Map[String, String], Map[String, Int]) => Unit)(implicit pos: Position) =
      testWithInfoTime(s"""[$strategyName] test SAT: "$name"""") {
        withExecuteFile(name) { solver =>
          solver.getModel() match {
            case Some((sModel, iModel)) => assertions(sModel, iModel)
            case None                   => fail()
          }
        }
      }
    def testFileUNSAT(name: String)(implicit pos: Position) =
      testWithInfoTime(s"""[$strategyName] test UNSAT: "$name"""") {
        withExecuteFile(name) { solver => assert(solver.getModel().isEmpty) }
      }

    // 非線形算術
    testSAT("""
(declare-const x String)
(declare-const i Int)
(assert (= (str.len x) (* i i)))
(assert (> i 1))
(check-sat)
(get-model)
""") { (sm, im) =>
      val x = sm("x")
      val i = im("i")
      assert(i > 1)
      assert(x.length == i * i)
    }

    testFileSAT("deleteall") { (sm, _) =>
      val (x0, x1, y0, y1, xy) = (sm("x0"), sm("x1"), sm("y0"), sm("y1"), sm("xy"))
      assert(x1 == x0.replaceAll("<script>", ""))
      assert(y1 == y0.replaceAll("<script>", ""))
      assert(xy == x1 ++ y1)
      assert(xy == "<script>")
    }

    testFileUNSAT("concat_unsat_03")

    testFileSAT("concat_delete") { (m, _) =>
      val (xy, x, y, z) = (m("xy"), m("x"), m("y"), m("z"))
      assert(xy == x ++ y)
      assert(z == xy.replaceAll("<script>", ""))
      assert("<script>".r.matches(z))
    }

    // // PreImageStrategy はモデル生成に失敗 (関数的でないから)
    // testFileSAT("replace_some_1") { (m, _) =>
    //   val (x, y) = (m("x"), m("y"))
    //   assert("a+".r.matches(x))
    //   assert("(ab)+".r.matches(y))
    // }

    testFileUNSAT("replace_some_2")

    testFileSAT("replaceall_int") { (m, _) =>
      val (x, y, z) = (m("x"), m("y"), m("z"))
      assert("[ab]*".r.matches(x))
      assert(y == x.replaceAll("ab", "c"))
      assert(z == y.replaceAll("ac", "aaaa"))
      assert(x.length + 5 <= z.length)
    }

    // Simple replace_pcre_all (match constant)
    testSAT("""
(declare-const x String)
(declare-const y String)

(assert (= y (str.replace_pcre_all x (str.to_pcre "aab") (pcre.replacement "b"))))
(assert (str.in.re y (re.++ re.all (str.to.re "aab") re.all)))
(check-sat)
(get-model)
""") { (sModel, iModel) =>
      val (x, y) = (sModel("x"), sModel("y"))
      assert(y == x.replaceAll("aab", "b"))
      assert(".*aab.*".r.matches(y))
      ()
    }

    // Delete all b+. Should be equivalent to (replace_all x "b" "")
    testSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "a"))))
(assert (= y (str.replace_pcre_all x (pcre.+ (str.to_pcre "b")) (pcre.replacement ""))))
(assert (str.in.re y (re.* (str.to.re "a"))))
(check-sat)
(get-model)
""") { (sm, _) =>
      val (x, y) = (sm("x"), sm("y"))
      assert(x.matches("^a*$"))
      assert(y == x.replaceAll("b+", ""))
      assert(y.matches("^a*$"))
    }

    // Unsat case.
    testUNSAT(
      """
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (= y (str.replace_pcre x (pcre.+ (str.to_pcre "ab")) (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)
"""
    )

    // Ensure replace_pcre replaces only first match
    testSAT(
      """
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (= y (str.replace_pcre x (str.to_pcre "ab") (pcre.replacement ""))))
(assert (str.in.re y (re.comp (str.to.re ""))))
(check-sat)
"""
    ) { (sm, im) =>
      val (x, y) = (sm("x"), sm("y"))
      assert("^(ab)*$".r.matches(x))
      assert(y == x.replaceFirst("ab", ""))
      assert(y != "")
    }

    // Ensure replace_pcre_all matches the longest match if many exist
    testUNSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (re.+ (str.to.re "ab"))))
(assert (= y (str.replace_pcre_all x (pcre.+ (str.to_pcre "ab")) (pcre.replacement "a"))))
(assert (str.in.re y (re.comp (str.to.re "a"))))
(check-sat)
""")

    // The following two tests shows order in PCRE alternation matters for some situations.
    testFileSAT("pcre_precedence_sat") { (sm, _) =>
      val (x, y) = (sm("x"), sm("y"))
      assert(x.matches("^(ab|abb)*$"))
      assert(y == x.replaceFirst("(ab|abb)+", ""))
      assert(y != "")
    }

    testFileUNSAT("pcre_precedence_unsat")

    // pcre.group
    testUNSAT("""
(declare-const x String)
(declare-const y String)

(assert (str.in.re x (str.to.re "ab")))
(assert (= y (str.replace_pcre
                 x
                 (pcre.++
                   (pcre.group (str.to_pcre "a"))
                   (pcre.group (str.to_pcre "b")))
                 (pcre.replacement 2 1 0))))
(assert (str.in.re y (re.comp (str.to.re "baab"))))
(check-sat)
""")

//    testFileSAT("group_sc") { (sm, _) =>
//      val (x, y) = (sm("x"), sm("y"))
//      assert(y == x.replaceFirst("\\{(.*?):(.*?)\\}", "<$1>$2</$1>"))
//      assert(y.matches("^.*<sc>.*</sc>.*$"))
//    }

    implicit class AtMostSubstring(s: String) {
      def atmostSubstring(idx: Int, len: Int): String = {
        if (0 <= idx && idx < s.length && 0 < len) s.substring(idx, idx + scala.math.min(len, s.length - idx))
        else ""
      }
    }

    // Simple substr test (sat case)
    testSAT("""
(declare-const x String)
(declare-const y String)
(declare-const i Int)

(assert (str.in.re x (re.+ (str.to.re "ab"))))
(assert (and (<= 0 i) (< i (str.len x))))
(assert (= y (str.substr x i 2)))
(assert (str.in.re y (re.comp (str.to.re "ab"))))

(check-sat)
""") {
      case (sModel, iModel) =>
        val (x, y, i) = (sModel("x"), sModel("y"), iModel("i"))
        assert("(ab)+".r.matches(x))
        assert(0 <= i && i < x.length)
        assert(y == x.atmostSubstring(i, 2))
        assert(!"ab".r.matches(y))
    }

    testSAT(""";; Bug fixed on 2021-07-05
(declare-const x String)
(declare-const i Int)
(assert (str.in.re x (str.to.re "abcaabd")))
(assert (= i (str.indexof x "abcabd" 0)))
(check-sat)
(get-model)
""") { (_, m) => assert(m("i") == -1) }

    testFileSAT("indexof_sat") { (m, _) =>
      val (x, y) = (m("x"), m("y"))
      assert(y == x.atmostSubstring(x.indexOf("aab"), x.length))
      assert(!"aab.*".r.matches(y))
    }

    testFileUNSAT("indexof")

    testFileSAT("substr_zip_sat") { (sm, _) =>
      val (x, y, z) = (sm("x"), sm("y"), sm("z"))
      assert(z == x.atmostSubstring(0, y.length))
      assert(z.length != x.length)
    }

    testFileUNSAT("substr_zip_unsat")

    // ???
    testSAT("""
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(assert (not (= (str.len x) (str.len y))))
(assert (= z (str.substr x 0 (- (str.len x) 1))))
(assert (= w (str.substr y 0 (- (str.len y) 1))))
(assert (= (str.len z) (str.len w)))
(check-sat)
(get-model)
""") { (m, _) => () }

    testFileUNSAT("concat_prefix_suffix")

    testFileUNSAT("cat_pre_suf")

    testFileSAT("insert_script") { (sm, im) =>
      val (x, y, z, p, s, l) = (sm("x"), sm("y"), sm("z"), sm("p"), sm("s"), im("l"))
      assert(x != "<script>")
      assert(p == x.atmostSubstring(0, l))
      assert(s == x.atmostSubstring(l, x.length - l))
      assert(z == p ++ y ++ s)
      assert(0 < y.length && y.length <= 6)
      assert(z == "<script>")
    }

    testFileSAT("reverse_indexof_sat") { (sm, _) =>
      val (x, y) = (sm("x"), sm("y"))
      assert(x.matches("^b*a*$"))
      assert(y == x.reverse)
      assert(!(y.indexOf("a") < y.indexOf("b")))
    }

    testFileUNSAT("reverse_indexof_unsat")

    testFileUNSAT("substr_equiv")

    testFileSAT("for_slide") { (sm, im) =>
      val (x, p, s, y, z, i, j) = (sm("x"), sm("p"), sm("s"), sm("y"), sm("z"), im("i"), im("j"))
      assert(x.matches("^(ab)*$"))
      assert(y.matches("^(ab)*$"))
      assert(j == i)
      assert(p == x.atmostSubstring(0, j))
      assert(s == x.atmostSubstring(j, x.length - j))
      assert(z == p ++ y ++ s)
      assert(!z.matches("^(ab)*$"))
    }

    if (strategyName != "jssst")
      testFileSAT("insert_opt") { (sm, im) =>
        val (x, y, z, i) = (sm("x"), sm("y"), sm("z"), im("i"))
        def insert(x: String, y: String, i: Int): String =
          y.substring(0, i) ++ x ++ y.substring(i, y.length)
        assert(x.matches("^(ab)*$"))
        assert(y.matches("^(ab)*$"))
        assert(z == insert(x, y, i))
        assert(!z.matches("^(ab)*$"))
      }

    testFileUNSAT("count_char_1")
    testFileSAT("count_char_2") { (m, _) =>
      val x = m("x")
      assert(x == "aaaaabbbbb")
    }
  }
}
