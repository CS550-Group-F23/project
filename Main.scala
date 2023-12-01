//> using scala "3.2.0"
//> using jar "stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object Project {
  def matrixSizeCheck(A: List[List[BigInt]], x: List[BigInt]): Boolean = {
    A match {
      case Cons(head, tail) => head.size == x.size && matrixSizeCheck(tail, x)
      case Nil()            => true
    }
  }

  def matmul(A: List[List[BigInt]], x: List[BigInt]): List[BigInt] = {
    require(A.size != 0 && x.size != 0 && matrixSizeCheck(A, x))

    def dot(lhs: List[BigInt], rhs: List[BigInt]): BigInt = {
      require(lhs.size == rhs.size)

      (lhs, rhs) match {
        case (Cons(h1, t1), Cons(h2, t2)) => h1 * h2 + dot(t1, t2)
        case (Nil(), Nil())               => 0
      }
    }

    A match {
      case Cons(head, Nil()) => Cons(dot(head, x), Nil())
      case Cons(head, tail)  => Cons(dot(head, x), matmul(tail, x))
      case Nil()             => Nil()
    }
  }

  def w_in(t: BigInt)(i: BigInt)(x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && x.size > 0)
    decreases(i)

    if (i >= x.size) 0
    else if (i == 0) x.head
    else w_in(t)(i - 1)(x.tail)
  }

  def indexTo(A: List[BigInt], index: BigInt): BigInt = {
    require(A.size >= 0 && index >= 0)

    A match {
      case Nil() => 0
      case _ =>
        if (index == 0) A.head
        else indexTo(A.tail, index - 1)
    }
  }

  def a_in(t: Int)(i: Int)(A: List[List[BigInt]]): BigInt = {
    require(t >= 0 && i >= 0 && A.size > 0)
    decreases(i)

    if (i == 0) indexTo(A.head, t)
    else if (i >= A.size) 0
    else {
      if (t == 0) 0
      else a_in(t - 1)(i - 1)(A.tail)
    }
  }

  def y_in(t: Int)(i: Int)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0)
    if (i > 0 && t > 0) y_out(t - 1)(i - 1)(A, x)
    else 0
  }

  def y_out(t: Int)(i: Int)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0)
    y_in(t)(i)(A, x) + a_in(t)(i)(A) * w_in(t)(i)(x)
  }

  // def submatrix(A: Seq[Seq[BigInt]], n: Int): Seq[Seq[BigInt]] = {
  //   A.slice(0,n).map(row => row.slice(0,n))
  // }

  // val A: Seq[Seq[BigInt]] = Seq(Seq(1, 2, 3), Seq(4, 5, 6), Seq(7, 8, 9))
  // val x: Seq[BigInt] = Seq(3, 2, 1)

  // def w_in(t: Int)(i: Int): BigInt = {
  //   if (i < x.length)
  //     x(i.toInt)
  //   else
  //     0
  // }

  // def a_in(t: Int)(i: Int): BigInt = {
  //   if(t >= 0 && i >= 0 && t - i >= 0 && t - i < A.length)
  //     A(t-i)(i)
  //   else
  //     0
  // }

  // def y_in(t: Int)(i: Int): BigInt = {
  //   if (i == 0)
  //     0
  //   else
  //     y_out(t-1)(i-1)
  // }

  // def y_out(t: Int)(i: Int): BigInt = {
  //   //require(t >= 0 && i >= 0)
  //   val thing = y_in(t)(i) + a_in(t)(i) * w_in(t)(i)
  //   print(s"y_out t = $t\t i = $i res=$thing\n")
  //   thing
  // } ensuring(res => ((t < i) || (t >= i+i-1) || res == matmul(submatrix(A,i+1),x.slice(0,i+1))(t-i)))

  // def main(args: Array[String]): Unit = {
  //   val comparison = matmul(submatrix(A,2),x.slice(0,2))
  //   print(s"comparison = $comparison")
  //   for(t <- 1 until 10) {
  //     val res = y_in(t)(2)
  //     val res2 = y_out(t)(2)
  //     print(s"t = $t\t y_in = $res\t y_out = $res2\n")
  //   }
  // }

  def main(args: Array[String]): Unit = {
    val A = List(List[BigInt](1, 2), List[BigInt](3, 4))
    val x = List[BigInt](5, 6)
    println(matmul(A, x).toString())
    
    for (i <- 0 until 5) {
      println(y_out(i)(2)(A, x))
    }
  }
}
