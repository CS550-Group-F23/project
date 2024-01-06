//> using scala "3.2.0"
//> using jar "../../../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object gemvRef {
  def isRectangular(A: List[List[BigInt]]): Boolean = {
    A match {
      case Cons(head, Nil()) => true
      case Cons(head, tail) =>
        head.size == tail.head.size && isRectangular(tail)
      case Nil() => true
    }
  }
  def inputArraysCheck(A: List[List[BigInt]], x: List[BigInt]): Boolean = {
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
  require(A.size >= 0 && X.size >= 0 && inputArraysCheck(A, X) && gas >= 0)
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
}