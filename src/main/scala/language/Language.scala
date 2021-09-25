package com.github.kmn4.expresso.language

import com.github.kmn4.expresso._
import com.github.kmn4.expresso.machine._
import com.github.kmn4.expresso.math._

trait ParikhLanguage[C, I] {
  def toParikhAutomaton(alphabet: Set[C]): ParikhAutomaton[Int, C, Int, I]
  def usedAlphabet: Set[C]
}

object ParikhLanguage {
  case class FromRegExp[C, I](val re: RegExp[C]) extends ParikhLanguage[C, I] {

    def usedAlphabet: Set[C] = re.usedAlphabet

    def toParikhAutomaton(alphabet: Set[C]): ParikhAutomaton[Int, C, Int, I] =
      re.toNFA(alphabet).toDFA.toParikhAutomaton.renamed
  }

}
