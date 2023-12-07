//> using scala "3.2.0"
//> using jar "../../../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object Gemv {
  def matrixSizeCheck(A: List[List[BigInt]], x: List[BigInt]): Boolean = {
    def isRectangular(A: List[List[BigInt]]): Boolean = {
      A match {
        case Cons(head, Nil()) => true
        case Cons(head, tail) =>
          head.size == tail.head.size && isRectangular(tail)
        case Nil() => true
      }
    }

    A.size == x.size && isRectangular(A)
  }

  def matmul(A: List[List[BigInt]], x: List[BigInt]): List[BigInt] = {
    require(A.size >= 0 && x.size >= 0 && matrixSizeCheck(A, x))

    def addVector(lhs: List[BigInt], rhs: List[BigInt]): List[BigInt] = {
      require(lhs.size == rhs.size)

      (lhs, rhs) match {
        case (Cons(h1, t1), Cons(h2, t2)) => Cons(h1 + h2, addVector(t1, t2))
        case (Nil(), Nil())               => Nil()
      }
    }.ensuring(_.size == lhs.size)

    def emv(k: BigInt, v: List[BigInt]): List[BigInt] = {
      v match {
        case Cons(head, Nil()) => Cons(k * head, Nil())
        case Cons(head, tail)  => Cons(k * head, emv(k, tail))
        case Nil()             => Nil()
      }
    }.ensuring(res => res.size == v.size)

    A match {
      case Cons(head, Nil()) => emv(x.head, head)
      case Cons(head, tail) =>
        addVector(emv(x.head, head), matmul(tail, x.tail))
      case Nil() => Nil()
    }
  }

  def takeList[T](n: BigInt, list: List[T]): List[T] = {
    require(n >= 0 && n <= list.size)
    if (n == 0) Nil()
    else {
      list match {
        case Cons(head, tail) => Cons(head, takeList(n - 1, tail))
        case Nil()            => assert(false)
      }
    }
  }

  def w_in(t: BigInt)(i: BigInt)(x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && x.size >= 0)
    decreases(i)

    if (i >= x.size) 0
    else if (i == 0) x.head
    else w_in(t)(i - 1)(x.tail)
  }

  def indexTo(A: List[BigInt], index: BigInt): BigInt = {
    require(A.size >= 0)

    if (index <= 0) 0
    else {
      A match {
        case Nil() => 0
        case _ =>
          if (index == 0) A.head
          else indexTo(A.tail, index - 1)
      }
    }
  }

  def a_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]]): BigInt = {
    require(t >= 0 && i >= 0 && A.size >= 0)
    decreases(i)

    if (A.size == 0) 0
    else if (i == 0) indexTo(A.head, t)
    else if (i >= A.size) 0
    else {
      if (t == 0) 0
      else a_in(t - 1)(i - 1)(A.tail)
    }
  }

  def y_in(
      t: BigInt
  )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
    if (i > 0 && t > 0) y_out(t - 1)(i - 1)(A, x)
    else 0
  }

  def y_out(
      t: BigInt
  )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
    y_in(t)(i)(A, x) + a_in(t)(i)(A) * w_in(t)(i)(x)
  }.ensuring(res =>
    (i >= x.length && res == indexTo(
      matmul(A, x),
      t - i
    )) || (i < x.length && res == indexTo(
      matmul(takeList(i + 1, A), takeList(i + 1, x)),
      t - i
    ))
  )

  def output(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && matrixSizeCheck(A, x))
    y_in(t)(x.length)(A, x)
  }.ensuring(res => res == outputSpec(t)(A, x))

  def outputSpec(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && A.size >= 0 && matrixSizeCheck(A, x))

    val res = matmul(A, x)

    if (t < x.length) 0
    else if (t - x.size < res.size) indexTo(res, t - x.size)
    else 0
  }

  def main(args: Array[String]): Unit = {
    // 1 3    5
    // 2 4    6
    val A = List(List[BigInt](1, 2), List[BigInt](3, 4))
    val x = List[BigInt](5, 6)

    // println(matmul(A, x).toString())

    // print("Expected\tGot\n")
    // for (t <- 0 until 10) {
    //   printf("%d\t\t%d\n", output(t)(A, x), outputSpec(t)(A, x))
    // }
  }
}
