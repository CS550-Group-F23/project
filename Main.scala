//> using scala "3.2.0"
//> using jar "stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

object Project {
/*
  def halfAdder(a: UInt, b: UInt): UInt = {
    require(a.width == 1 && b.width == 1)

    val s = a ^ b
    val c = a & b
    val res = c ## s

    res
  }.ensuring(res => res.width == 2 && res.data == a.data + b.data)

  def fullAdder(a: UInt, b: UInt, cIn: UInt): UInt = {
    require(a.width == 1 && b.width == 1 && cIn.width == 1)

    val s = a ^ b ^ cIn
    val c = ((a ^ b) & cIn) | (a & b)
    val res = c ## s

    res
  }.ensuring(res => res.width == 2 && res.data == a.data + b.data + cIn.data)

  def rca4(a: UInt, b: UInt, cIn: UInt): UInt = {
    require(a.width == 4 && b.width == 4 && cIn.width == 1)

    var res = fullAdder(a.get(0), b.get(0), cIn)
    res = fullAdder(a.get(1), b.get(1), res.get(1)) ## res.get(0)
    res = fullAdder(a.get(2), b.get(2), res.get(2)) ## res.get(1, 0)
    res = fullAdder(a.get(3), b.get(3), res.get(3)) ## res.get(2, 0)

    res
  }.ensuring(res => res.width == 5 && res.data == a.data + b.data + cIn.data)

  def rca(n: Int)(a: UInt, b: UInt, cIn: UInt): UInt = {
    decreases(n)
    require(n > 0 && n < 61)
    require(a.width == n && b.width == n && cIn.width == 1)

    if(n == 1) {
      fullAdder(a.get(0), b.get(0), cIn)
    } else {
      val prev = rca(n-1)(a.get(n-2, 0), b.get(n-2, 0), cIn)
      fullAdder(a.get(n-1), b.get(n-1), prev.get(n-1)) ## prev.get(n-2, 0)
    }
  }.ensuring(res => res.width == n+1 && res.data == a.data + b.data + cIn.data)
*/

  def matmul(A: Seq[Seq[BigInt]], x: Seq[BigInt]): Seq[BigInt] = {
    A.map(row => row.zip(x).map(a => a._1 * a._2).sum)
  }

  def submatrix(A: Seq[Seq[BigInt]], n: Int): Seq[Seq[BigInt]] = {
    A.slice(0,n).map(row => row.slice(0,n))
  }

  val A: Seq[Seq[BigInt]] = Seq(Seq(1, 2, 3), Seq(4, 5, 6), Seq(7, 8, 9))
  val x: Seq[BigInt] = Seq(3, 2, 1)

  def w_in(t: Int)(i: Int): BigInt = {
    if (i < x.length)
      x(i.toInt)
    else 
      0
  }

  def a_in(t: Int)(i: Int): BigInt = {
    if(t >= 0 && i >= 0 && t - i >= 0 && t - i < A.length)
      A(t-i)(i)
    else
      0
  }

  def y_in(t: Int)(i: Int): BigInt = {
    if (i == 0)
      0
    else
      y_out(t-1)(i-1)
  }

  def y_out(t: Int)(i: Int): BigInt = {
    //require(t >= 0 && i >= 0)
    val thing = y_in(t)(i) + a_in(t)(i) * w_in(t)(i)
    print(s"y_out t = $t\t i = $i res=$thing\n")
    thing
  } ensuring(res => ((t < i) || (t >= i+i-1) || res == matmul(submatrix(A,i+1),x.slice(0,i+1))(t-i)))

  def main(args: Array[String]): Unit = {
    val comparison = matmul(submatrix(A,2),x.slice(0,2))
    print(s"comparison = $comparison")
    for(t <- 1 until 10) {        
      val res = y_in(t)(2)
      val res2 = y_out(t)(2)
      print(s"t = $t\t y_in = $res\t y_out = $res2\n")
    }
  }
}
