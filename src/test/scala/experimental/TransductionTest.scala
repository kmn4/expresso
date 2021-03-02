package com.github.kmn4.sst.experimental

import org.scalatest.funsuite.AnyFunSuite
import com.github.kmn4.sst.MNFT
import com.github.kmn4.sst.NSST
import com.github.kmn4.sst.{Cop1, Cop2}
import com.github.kmn4.sst.Cop
import com.github.kmn4.sst.ParikhSolver
import com.github.kmn4.sst.ParikhSST

class TransductionTest extends AnyFunSuite {
  type NFT[Q, A, B] = MNFT[Q, A, Seq[B]]
  implicit def nftSST[Q, A, B](nft: NFT[Q, A, B]): NSST[Q, A, B, Unit] = {
    NSST(
      nft.states,
      nft.in,
      Set(()),
      nft.edges.map {
        case (q, a, bs, r) =>
          (q, a, Map(() -> (Cop1(()) :: bs.map(Cop2.apply).toList)), r)
      },
      nft.initials.head,
      for {
        (q, s) <- nft.partialF
      } yield (q, s.map(bs => (Cop1(()) :: bs.map(Cop2.apply).toList)))
    )
  }
  def concatTransducer(arity: Int, alphabet: Set[Char]): NFT[Int, Either[Char, Int], Char] = {
    val states = (0 until arity).toSet
    val inSet = alphabet.map(Left.apply) ++ (0 to arity - 2).map(Right.apply).toSet
    val loop =
      for {
        q <- states
        a <- alphabet
      } yield (q, Left(a), Seq(a), q)
    val next =
      for {
        q <- 0 to arity - 2
      } yield (q, Right(q), Seq.empty, q + 1)
    MNFT(
      states,
      inSet,
      loop ++ next,
      Set(0),
      Map(arity - 1 -> Set(""))
    )
  }
  test("""y = x.x
|y| = i""") {
    val alphabet = "ab".toSet
    val pa = ParikhSolver.ParikhLanguage.Length("i").toParikhAutomaton(alphabet)
    val lang = ParikhAutomaton(
      0,
      pa.states,
      pa.inSet,
      pa.ls,
      pa.is,
      pa.edges,
      pa.q0,
      pa.acceptRelation.head,
      pa.acceptFormulas
    )
    val f = concatTransducer(2, alphabet).toParikhSST[Int, String]
    val preImage = new Transduction.ParikhTransduction(f).preImage(lang, 0)
    for (clause <- preImage) info(s"$clause")

  }
}
