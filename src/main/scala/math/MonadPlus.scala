package com.github.kmn4.expresso.math

trait MonadPlus[M[_]] {
  def empty[T]: M[T]
  def apply[T](t: T): M[T]
  def flatMap[T, S](m: M[T])(f: T => M[S]): M[S]
  def concat[T](m: M[T], n: M[T]): M[T]
}

object MonadPlus {
  def apply[M[_]: MonadPlus] = implicitly[MonadPlus[M]]

  implicit class MonadPlusOps[M[_]: MonadPlus, T](m: M[T]) {
    def flatMap[S](f: T => M[S]): M[S] = MonadPlus[M].flatMap(m)(f)
    def concat(n: M[T]): M[T] = MonadPlus[M].concat(m, n)

    def >>=[S](f: T => M[S]): M[S] = this.flatMap(f)
    def ++(n: M[T]): M[T] = this.concat(n)

    def map[S](f: T => S): M[S] = this >>= (f andThen MonadPlus[M].apply)
  }

  implicit val seqMonadPlus: MonadPlus[Seq] = new MonadPlus[Seq] {
    def empty[T]: Seq[T]                                 = Seq.empty
    def apply[T](t: T): Seq[T]                           = Seq(t)
    def flatMap[T, S](m: Seq[T])(f: T => Seq[S]): Seq[S] = m.flatMap(f)
    def concat[T](m: Seq[T], n: Seq[T]): Seq[T]          = m ++ n
  }
}
