//> using scala "3.2.0"
//> using jar "../../../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object gemv {
  def isRectangular(A: List[List[BigInt]]): Boolean = {
    A match {
      case Cons(head, Nil()) => true
      case Cons(head, tail) =>
        head.size == tail.head.size && isRectangular(tail)
      case Nil() => true
    }
  }
  def matrixSizeCheck(A: List[List[BigInt]], x: List[BigInt]): Boolean = {
    A.size == x.size && isRectangular(A)
  }

  def emv(k: BigInt, v: List[BigInt]): List[BigInt] = {
  v match {
      case Cons(head, Nil()) => Cons(k * head, Nil())
      case Cons(head, tail)  => Cons(k * head, emv(k, tail))
      case Nil()             => Nil()
  }
  }.ensuring(res => res.size == v.size)

  def addVector(lhs: List[BigInt], rhs: List[BigInt]): List[BigInt] = {
  require(lhs.size == rhs.size)

  (lhs, rhs) match {
      case (Cons(h1, t1), Cons(h2, t2)) => Cons(h1 + h2, addVector(t1, t2))
      case (Nil(), Nil())               => Nil()
  }
  }.ensuring(res => res.size == lhs.size)

  def matmul(
      A: List[List[BigInt]],
      X: List[BigInt],
      gas: BigInt
  ): List[BigInt] = {
  require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X) && gas >= 0)
  decreases(gas)

  if (gas > 0) {
      A match {
      case Cons(head, tail) =>
          if (tail.size == 0 || gas == 1) emv(X.head, head)
          else {
          addVector(emv(X.head, head), matmul(tail, X.tail, gas - 1))
          }
      case Nil() => Nil()
      }
  } else {
      Nil()
  }
  }.ensuring(res => (A.size == 0 && res.size == 0) || (gas == 0 && res.size == 0) || (A.head.size == res.size))

  def indexTo(A: List[BigInt], index: BigInt): BigInt = {
  require(A.size >= 0)

  if (index < 0) BigInt(0)
  else {
    A match {
      case Nil() => BigInt(0)
      case Cons(a, aa) =>
        if (index == 0) a
        else indexTo(aa, index - 1)
    }
  }
  }.ensuring(res => (index >= 0 && index < A.size && res == A(index)) || ((index < 0 || index >= A.size) && res == 0))

  def w_in(t: BigInt)(i: BigInt)(x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && x.size >= 0)
    decreases(i)

    if (i >= x.size) BigInt(0)
    else if (i == 0) x.head
    else w_in(t)(i - 1)(x.tail)
  }.ensuring(res => res == indexTo(x, i))

  def a_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]]): BigInt = {
    require(t >= 0 && i >= 0 && A.size >= 0)
    decreases(i)

    A match {
      case Nil() => BigInt(0)
      case Cons(a, aa) => {
        if (i == 0) indexTo(a, t)
        else if (i >= A.size || t == 0) BigInt(0)
        else a_in(t - 1)(i - 1)(aa)
      }
    }
  }.ensuring(res =>
    // If-Then-Else(i <= t && i < A.size && t-i < A.head.size, res == indexTo(A(i), t-i)) && ite(t-i < A(i).size, true, res == 0), res == 0)
    ((i <= t && i < A.size && res == indexTo(A(i), t - i) && ((t - i < A(i).size) || (t - i >= A(i).size && res == 0)))
      || ((i > t || i >= A.size) && res == 0))
  )

  def y_in(
      t: BigInt
  )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
    if (i > 0 && t > 0) {
      y_out(t - 1)(i - 1)(A, x)
    } else BigInt(0)
  }.ensuring(res => res == 0 || (i > 0 && t > 0))

  def y_out(
      t: BigInt
  )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
    y_in(t)(i)(A, x) + a_in(t)(i)(A) * w_in(t)(i)(x)
  }

  def output(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && matrixSizeCheck(A, x))
    y_in(t)(x.size)(A, x)
  }
}