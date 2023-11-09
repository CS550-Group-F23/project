import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

object Project {

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

}
