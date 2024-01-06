import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check
import gemvRef.inputArraysCheck

object gemvImpl {
def y_out(t: BigInt)(i: BigInt)(A: List[List[BigInt]], W: List[BigInt]): BigInt = {
require((i >= 0) && (t >= 0) && inputArraysCheck(A,W))
y_in(t)(i)(A,W)+a_in(t)(i)(A,W)*w_in(t)(i)(A,W)
}
def a_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]], W: List[BigInt]): BigInt = {
require((i >= 0) && (t >= 0) && inputArraysCheck(A,W))
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
require((i >= 0) && (t >= 0) && inputArraysCheck(A,W))
if (!(i<W.size)) { 0 } else {
W(i)
}
}
def y_in(t: BigInt)(i: BigInt)(A: List[List[BigInt]], W: List[BigInt]): BigInt = {
require((i >= 0) && (t >= 0) && inputArraysCheck(A,W))
if (i == 0) { 0 } else {
if (t <= 0) { 0 } else {
y_out(t - 1)(i - 1)(A,W)
}
}
}
}