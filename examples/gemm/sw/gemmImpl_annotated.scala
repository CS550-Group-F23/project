object gemm {
def matrixSizeCheck(A: List[List[Int]], B: List[List[Int]]): Boolean = true
def y_out(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
y_in(t)(i,j)(A,B)+a_in(t)(i,j)(A,B)*b_in(t)(i,j)(A,B)
}
def a_out(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
a_in(t)(i,j)(A,B)
}
def b_out(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
b_in(t)(i,j)(A,B)
}
def A_in(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
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
def B_in(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
if (!(0<B.size) || !(j<B.size)) { 0 } else {
if (t < j) {
0
} else if (t < j+B(j).size) {
B(j)(t-j)
} else {
0
} 
}
}
def y_in(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
if (t <= 0) { 0 } else {
y_out(t - 1)(i,j)(A,B)
}
}
def a_in(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
if (j == 0) { A_in(t)(i,0)(A,B) } else {
if (t <= 0) { 0 } else {
a_out(t - 1)(i,j - 1)(A,B)
}
}
}
def b_in(t: Int)(i: Int, j: Int)(A: List[List[Int]], B: List[List[Int]]): Int = {
require((i >= 0) && (j >= 0) && (t >= 0) && matrixSizeCheck(A,B))
if (i == 0) { B_in(t)(0,j)(A,B) } else {
if (t <= 0) { 0 } else {
b_out(t - 1)(i - 1,j)(A,B)
}
}
}
def main(args: Array[String]): Unit = {
    val A = List[List[Int]](List[Int](1,4,7),List[Int](2,5,8),List[Int](3,6,9))
    val B = List[List[Int]](List[Int](1,4,7),List[Int](2,5,8),List[Int](3,6,9))
    for (i <- 0 until 3) {
        for (j <- 0 until 3) {
            printf("out(i=%d,j=%d)=%d\n", i, j, y_out(6)(i, j)(A,B))
        }
    }
}
}