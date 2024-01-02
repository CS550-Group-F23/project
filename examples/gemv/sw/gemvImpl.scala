import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object gemv {
def y_out(t: BigInt)(i: BigInt)(A: List[List[BigInt]], W: List[BigInt]): BigInt = {
y_in(t)(i)(A,W) + a_in(t)(i)(A,W) * w_in(t)(i)(A,W)
}
def a_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]], W: List[BigInt]): BigInt = {
if (!(0<A.size) || !(i<A.size)) { 0 } else {
if (t < i) {
0
} else if (t < i+A(i).size) {
A(i)(t-i)
} else {
0
} 
}
}
def w_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]], W: List[BigInt]): BigInt = {
if (!(i<W.size)) { 0 } else {
W(i)
}
}
}