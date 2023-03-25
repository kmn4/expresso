package com.github.kmn4.expresso

import scala.util.control.NonLocalReturns._

object TopSort {
  case class Graph[A](nodes: Iterable[A], next: Map[A, Iterable[A]])
  def sort[A](graph: Graph[A]): Option[Seq[A]] // a -> b なら idx(a) > idx(b)
  = {
    val visited = collection.mutable.Set.empty[A]
    val res = collection.mutable.ArrayBuffer.empty[A]
    val numbered = collection.mutable.Set.empty[A]
    def number(a: A): Unit = {
      numbered += a
      res.append(a)
    }
    def dfs(node: A): Boolean /* 循環を検知したら true */ = returning {
      visited += node
      for (a <- graph.next(node) if !numbered(a))
        if (visited(a) || dfs(a)) throwReturn(true)
      number(node)
      throwReturn(false)
    }
    var toVisit = graph.nodes.toSet
    while (toVisit.nonEmpty) {
      val hd = toVisit.head
      if (dfs(hd)) return None
      toVisit --= visited
    }
    return Some(res.toSeq)
  }
}
