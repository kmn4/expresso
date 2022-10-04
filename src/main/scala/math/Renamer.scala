package com.github.kmn4.expresso.math

class Renamer[L] extends Function1[L, Int] {
  private type X = L
  private var _max = -1
  private val _map = collection.mutable.Map[X, Int]()
  def apply(x: X): Int = _map.getOrElseUpdate(
    x, {
      _max += 1
      _max
    }
  )
}
