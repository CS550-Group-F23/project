//> using scala "3.2.0"
//> using jar "../../../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object Gemv {
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

  def matmul(
      A: List[List[BigInt]],
      x: List[BigInt],
      n: BigInt
  ): List[BigInt] = {
    require(A.size >= 0 && x.size >= 0 && matrixSizeCheck(A, x) && n >= 0)
    

    def addVector(lhs: List[BigInt], rhs: List[BigInt]): List[BigInt] = {
      require(lhs.size == rhs.size)

      (lhs, rhs) match {
        case (Cons(h1, t1), Cons(h2, t2)) => Cons(h1 + h2, addVector(t1, t2))
        case (Nil(), Nil())               => Nil()
      }
    }.ensuring(_.size == lhs.size)

    def emv(k: BigInt, v: List[BigInt], n: BigInt): List[BigInt] = {
      require(n >= 0)
      decreases(n)
      if (n > 0) {
        v match {
          case Cons(head, Nil()) => Cons(k * head, Nil())
          case Cons(head, tail)  => Cons(k * head, emv(k, tail, n - 1))
          case Nil()             => Nil()
        }
      } else {
        Nil()
      }
    }.ensuring(res => (v.size > n && res.size == n) || (v.size <= n && res.size == v.size))

    val thing = A match {
      case Cons(head, tail) =>
        if (tail.size == 0 || n == 1) emv(x.head, head, n)
        else
          addVector(emv(x.head, head, n), matmul(tail, x.tail, n))
      case Nil() => Nil()
    }
    //println(thing.toString())
    thing
  }.ensuring(res => (A.size == 0 && res.size == 0) || (A.head.size > n && res.size == n) || (A.head.size <= n && res.size == A.head.size))

  def vecAdd(a: List[BigInt], b: List[BigInt], n: BigInt): List[BigInt] = {
    require(n >= 0 && a.size >= 0 && a.size == b.size)
    decreases(n)

    if (n == 0) Nil()
    else
      (a, b) match {
        case (Cons(h1, t1), Cons(h2, t2)) =>
          Cons(h1 + h2, vecAdd(t1, t2, n - 1))
        case (Nil(), Nil()) => Nil()
      }
  }.ensuring(res =>
    (a.size > n && res.size == n) || (a.size <= n && res.size == a.size)
  )
  
  def lemma3[T](
    A: List[T],
    n: BigInt
  ): Boolean = {
    require(A.size > 0 && n > 0)
    A.head == A.take(n).head
  }.holds
  
  def lemma2(
    A: List[List[BigInt]],
    n: BigInt
  ): Unit = {
    require(isRectangular(A) && n >= 0)
    A match {
      case Cons(head, tail) => {
        if (n > 0) {
          check(lemma3(A, n))
          check(A.head == A.take(n).head)
          check(A.head.size == A.take(n).head.size)
          lemma2(tail, n-1)
        } else {
          check(A.take(n) == Nil())
        }
      }
      case Nil() => check(A.take(n) == Nil())
    }
    // if (n > 0) {
    //   A match {
    //     case Cons(head, Nil()) => assert(true)
    //     case Cons(head, tail) => assert(head.size == tail.head.size)
    //     case Nil() => assert(true)
    //   }
    //   lemma2(A, n- 1)
    // } else { 
      
    // }
    // A match {
    //   case Cons(a,aa) => {
    //     lemma2(aa, n)
    //   }
    //   case Nil() => {
    //     check(takeList(n,A) == Nil())
    //   }
    // }
  }.ensuring(isRectangular(A.take(n)))

  def lemma1(
      A: List[List[BigInt]],
      x: List[BigInt],
      n: BigInt
  ): Unit = {
    require(A.size >= 0 && x.size >= 0 && matrixSizeCheck(A, x) && n >= 0)
    decreases(n)

    check(A.take(n).size == x.take(n).size)
    lemma2(A, n)
    val a = matmul(A.take(n),x.take(n), n)
    val b = matmul(A, x, n)

    if(n == 0) {
      assert(true)
    } else {
      (A, x) match {
        case (Cons(h1, t1), Cons(h2, t2)) => {
          lemma1(t1, t2, n-1)
        }
        case (Nil(), Nil()) => {
          assert(A.take(n) == Nil())
          assert(x.take(n) == Nil())
          assert(b == Nil())
        }
      }
    }
  }.ensuring(matmul(A.take(n), x.take(n), n) == matmul(A, x, n))

  /*def takeList[T](n: BigInt, list: List[T]): List[T] = {
    require(n >= 0)
    decreases(n)
    if (n == 0) Nil()
    else {
      list match {
        case Cons(head, tail) => Cons(head, takeList(n - 1, tail))
        case Nil()            => Nil()
      }
    }
  }.ensuring(res =>
    (n <= list.size && res.size == n) || (n > list.size && res.size == list.size)
  )*/

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

  // def w_in(t: BigInt)(i: BigInt)(x: List[BigInt]): BigInt = {
  //   require(t >= 0 && i >= 0 && x.size >= 0)
  //   decreases(i)

  //   if (i >= x.size) 0
  //   else if (i == 0) x.head
  //   else w_in(t)(i - 1)(x.tail)
  // }

  // def a_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]]): BigInt = {
  //   require(t >= 0 && i >= 0 && A.size >= 0)
  //   decreases(i)

  //   if (A.size == 0) 0
  //   else if (i == 0) indexTo(A.head, t)
  //   else if (i >= A.size) 0
  //   else {
  //     if (t == 0) 0
  //     else a_in(t - 1)(i - 1)(A.tail)
  //   }
  // }

  // def y_in(
  //     t: BigInt
  // )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
  //   require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
  //   if (i > 0 && t > 0) y_out(t - 1)(i - 1)(A, x)
  //   else 0
  // }

  // def y_out(
  //     t: BigInt
  // )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
  //   require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
  //   y_in(t)(i)(A, x) + a_in(t)(i)(A) * w_in(t)(i)(x)
  // }.ensuring(res => res == indexTo(matmul(A, x, i), t - i))

  // def output(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
  //   require(t >= 0 && matrixSizeCheck(A, x))
  //   y_in(t)(x.length)(A, x)
  // }.ensuring(res => res == outputSpec(t)(A, x))

  // def outputSpec(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
  //   require(t >= 0 && A.size >= 0 && matrixSizeCheck(A, x))

  //   val res = matmul(A, x, x.size)

  //   if (t < x.length) 0
  //   else if (t - x.size < res.size) indexTo(res, t - x.size)
  //   else 0
  // }

  def main(args: Array[String]): Unit = {
    // 1 3    5
    // 2 4    6
    //val A = Cons[List[BigInt]](Cons[BigInt](BigInt("0"), Cons[BigInt](BigInt("0"), Nil[BigInt]())), Nil[List[BigInt]]()) // List[BigInt](1)
    //val x = Cons[BigInt](BigInt("-1"), Nil[BigInt]()) // List[BigInt](5)
//
    //println(matmul(A, x, 1))

    // println(matmul(A, x).toString())

    // print("Expected\tGot\n")
    // for (t <- 0 until 10) {
    //   printf("%d\t\t%d\n", output(t)(A, x), outputSpec(t)(A, x))
    // }
  }
}
