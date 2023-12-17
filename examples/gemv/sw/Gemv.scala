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

  def addVectorAssoc(A: List[BigInt], B: List[BigInt], C: List[BigInt]): Unit = {
    require(A.size == B.size && B.size == C.size) 

    (A, B, C) match {
      case (Cons(a, aa), Cons(b,bb), Cons(c,cc)) =>
        assert((a + b) + c == a + (b + c))
        addVectorAssoc(aa, bb, cc)
      case (Nil(), Nil(), Nil()) => assert(true)
    }

  }.ensuring(addVector(addVector(A,B), C) == addVector(A, addVector(B, C)))

  def addVectorCommutativity(A: List[BigInt], B: List[BigInt]): Unit = {
    require(A.size == B.size) 

    (A, B) match {
      case (Cons(a, aa), Cons(b,bb)) =>
        assert(a + b == b + a)
        addVectorCommutativity(aa, bb)
      case (Nil(), Nil()) => assert(true)
    }

  }.ensuring(addVector(A,B) == addVector(B,A))

  def matmul(
      A: List[List[BigInt]],
      x: List[BigInt],
      n: BigInt
  ): List[BigInt] = {
    require(A.size >= 0 && x.size >= 0 && matrixSizeCheck(A, x) && n >= 0)
    decreases(n)

    if (n > 0) {
      A match {
        case Cons(head, tail) =>
          if (tail.size == 0 || n == 1) emv(x.head, head)
          else {
            addVector(emv(x.head, head), matmul(tail, x.tail, n - 1))
          }
        case Nil() => Nil()
      }
    } else {
      Nil()
    }
    // println(thing.toString())
  }.ensuring(res =>
    (A.size == 0 && res.size == 0) || (n == 0 && res.size == 0) || (A.head.size == res.size)
  )

  def simpleSum(
    A: List[BigInt]
  ): BigInt = {
    A match {
      case Nil() => 0
      case Cons(h,t) => h + simpleSum(t)
    }
  }

  def simplestSumLemma(A: List[BigInt], x: BigInt): Unit = {
    A match {
      case Nil() => assert(true)
      case Cons(a,aa) => {
        simplestSumLemma(aa, x)
        // simpleSum(aa) + x == simpleSum(aa :+ x)
        check(a + simpleSum(aa) + x == a + simpleSum(aa :+ x))
        check(simpleSum(A) + x == a + simpleSum(aa :+ x))
        check(Cons(a, aa :+ x) == A :+ x)
        check(a + simpleSum(aa :+ x) == simpleSum(A :+ x))
      }
    }
  }.ensuring(simpleSum(A) + x == simpleSum(A :+ x))

  def reverseLemmaSimpler(
    A: List[BigInt]
  ): Unit = {

    A match {
      case (Nil()) => { check(true) }
      case (Cons(a,aa)) => {
        reverseLemmaSimpler(aa)
        check(a + simpleSum(aa.reverse) == a + simpleSum(aa))
        check(aa.reverse :+ a == A.reverse)
        simplestSumLemma(aa.reverse, a)
      }
    }

  }.ensuring(simpleSum(A) == simpleSum(A.reverse))

  def simplestMatmulLemma(
    A: List[List[BigInt]],
    X: List[BigInt],
    n: BigInt,
    an: List[BigInt],
    xn: BigInt
  ): Unit = { 
    require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X) && n >= 0)
    require(A.size == 0 || A.head.size == an.size)
    require(n > A.size)

    (A,X) match {
      case (Nil(),Nil()) => assert(true)
      case (Cons(a,aa), Cons(x,xx)) => {
        if (aa.size == 0 || n == 1) assert(true) 
        else {
          // addVector(matmul(aa, xx, n),emv(xn, an)) == matmul(aa :+ an, xx :+ xn, n)
          simplestMatmulLemma(aa, xx, n-1, an, xn)
          // Add emv(x,a) to both sides
          assert(addVector(emv(x,a), addVector(matmul(aa,xx,n-1), emv(xn,an))) == addVector(emv(x,a), matmul(aa :+ an, xx :+ xn, n-1)))
          // Associate LHS
          addVectorAssoc(emv(x,a), matmul(aa, xx, n-1), emv(xn,an))
          assert(addVector(emv(x,a), matmul(aa,xx,n-1)) == matmul(A, X, n))
          assert(addVector(emv(x,a), matmul(aa :+ an, xx :+ xn, n-1)) == matmul(A :+ an, X :+ xn, n)) 
        }
      }
    }

  }.ensuring((A.size == 0 && X.size == 0) || addVector(matmul(A, X, n),emv(xn, an)) == matmul(A :+ an, X :+ xn, n))

  def partitionList[T](A: List[T], n: BigInt): Unit = {
    require(n < A.size && n >= 0)
    if (n == 0) {
      assert(A.take(n) == Nil[T]())
      assert(A.drop(n) == A)
    } else {
      A match {
        case Nil[T]() => assert(true)
        case Cons(a,aa) => {
          partitionList(aa, n-1)
          check(A.take(n) == Cons(a, aa.take(n-1)))
        }
      }
    }
  }.ensuring(A == (A.take(n) ++ A.drop(n)))

  def howManyMoreFuckingLemmas[T](A: List[T], n: BigInt): Unit = {
    require(n < A.size && n >= 0)

    if (n == 0) {
      assert(A.drop(n) == A)
      assert(A.take(1).head == A(0))
    } else {
      A match {
        case Nil[T]() => {assert(true)}
        case Cons(a,aa) => {
          howManyMoreFuckingLemmas(aa, n-1)
          check(A.drop(n) == aa.drop(n-1))
          check(aa(n-1) == A(n))
        }
      }
    }
  }.ensuring(A.drop(n).take(1).head == A(n))

  def takeAppend[T](A: List[T], n: BigInt): Unit = {
    require(n < A.size && n >= 0)
    partitionList(A, n)
    ListSpecs.appendTakeDrop(A.take(n), A.drop(n), n+1)
    check(A.take(n+1) == A.take(n) ++ A.drop(n).take(1))
    howManyMoreFuckingLemmas(A, n)
  }.ensuring(A.take(n) :+ A(n) == A.take(n+1))
  /*
  def reverseLemma(
      A: List[List[BigInt]],
      X: List[BigInt],
      n: BigInt
  ): Unit = {
    require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X) && n >= 0)
    require(n >= A.size)
    require(matrixSizeCheck(A.reverse, X.reverse))

    (A,X) match {
      case (Nil(),Nil()) => assert(true)
      case (Cons(a,aa), Cons(x,xx)) => {
        if (aa.size == 0 || n == 1) assert(true) 
        else {
          // matmul(aa, xx, n-1) == matmul(aa.reverse, xx.reverse, n-1)
          reverseLemma(aa, xx, n-1)
          // addVector(matmul(aa.reverse, xx.reverse, n),emv(x, a)) == matmul(aa.reverse :+ a, xx.reverse :+ x, n)
          simplestMatmulLemma(aa.reverse, xx.reverse, n, a, x)
          assert(addVector(emv(x, a),matmul(aa,xx,n-1)) == matmul(A,X,n))
          assert(matmul(A,X,n) == addVector(emv(x, a), matmul(aa.reverse, xx.reverse, n-1)))
          addVectorCommutativity(emv(x, a), matmul(aa.reverse, xx.reverse, n-1))
          assert(matmul(aa.reverse, xx.reverse, n-1) == matmul(aa.reverse, xx.reverse, n))
          
          check(aa.reverse :+ a == A.reverse)
          check(xx.reverse :+ x == X.reverse)
        }
      }
    }

  }.ensuring(matmul(A, X, n) == matmul(A.reverse, X.reverse, n))
  */

  // def lemmaAdditivity(
  //     A: List[List[BigInt]],
  //     x: List[BigInt],
  //     n: BigInt
  // ): Unit = {
  //   require(A.size >= 0 && x.size >= 0 && matrixSizeCheck(A, x) && n >= 0)

  //   if (n == 0) {
  //     assert(true)
  //   } else {

  //   }

  // }.ensuring(res =>
  //   (n >= A.size && res == matmul(A,x,n - 1)) || (n < A.size && res == addVector(emv(x(n), A(n)), matmul(A, x, n - 1)))
  // )

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
          lemma2(tail, n - 1)
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
    val a = matmul(A.take(n), x.take(n), n)
    val b = matmul(A, x, n)

    if (n > 0) {
      (A, x) match {
        case (Cons(h1, t1), Cons(h2, t2)) => {
          lemma1(t1, t2, n - 1)
          if (t2.size == 0 || n == 1) {
            check(b == emv(x.head, A.head))
          } else {
            check(addVector(emv(h2, h1), matmul(t1, t2, n - 1)) == b)
          }
        }
        case (Nil(), Nil()) => {
          assert(A.take(n) == Nil())
          assert(x.take(n) == Nil())
          assert(b == Nil())
        }
      }
    } else {
      assert(matmul(A, x, n) == Nil())
    }

  }.ensuring(matmul(A.take(n), x.take(n), n) == matmul(A, x, n))

  def matmulGasLemma(A: List[List[BigInt]], X: List[BigInt], i: BigInt): Unit = {
    require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X))
    require(i >= A.size)
    (A,X) match { 
      case (Nil(), Nil()) => {
        assert(matmul(A,X,i) == Nil())
      }
      case (Cons(a, aa), Cons(x,xx)) => {
        if (aa.size == 0 || i == 1) {
          check(true)
        } else {
          matmulGasLemma(aa, xx, i-1)
          assert(matmul(A,X,A.size) == addVector(emv(x,a),matmul(aa,xx,A.size-1)))
          assert(matmul(A,X,i) == addVector(emv(x,a),matmul(aa,xx,i-1)))
        }
      }
    }
  }.ensuring(matmul(A,X,A.size) == matmul(A,X,i))

  def rectangularIndexLemma(A: List[List[BigInt]], n: BigInt): Unit = {
    require(A.size >= 0 && isRectangular(A))
    require(n >= 0 && n < A.size)

    if (n == 0) {
      assert(true)
    } else {
      A match {
        case Nil() => {assert(true)}
        case Cons(a,aa) => {
          rectangularIndexLemma(aa, n-1)
        }
      }
    }
  }.ensuring(A.size == 0 || (A.head.size == A(n).size))

  def linearIndexLemma(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(i > 0 && i < A.size)
    require(A.size > 0 && x.size > 0 && matrixSizeCheck(A, x))
    // matmul(A,x,i) == matmul(A.take(i), x.take(i), i)
    lemma1(A, x, i)
    // matmul(A.take(i), x.take(i), i) == matmul(A.take(i), x.take(i), i+1) 
    matmulGasLemma(A.take(i), x.take(i), i+1)
    
    // addVector(matmul(A.take(i),X.take(i),i+1),emv(x(i), A(i)) == matmul(A.take(i+1), X.take(i+1), i+1)
    lemma2(A, i)
    rectangularIndexLemma(A, i)
    simplestMatmulLemma(A.take(i), x.take(i), i + 1, A(i), x(i))
    takeAppend(A, i)
    takeAppend(x, i)
    check(addVector(matmul(A.take(i),x.take(i),i+1),emv(x(i), A(i))) == matmul(A.take(i+1), x.take(i+1), i+1))
    // matmul(A.take(i+1), x.take(i+1), i+1) == matmul(A,x,i+1)
    lemma2(A, i+1)
    lemma1(A, x, i+1)
  }.ensuring(addVector(matmul(A, x, i), emv(x(i), A(i))) == matmul(A, x, i + 1) )

  //def takeList[T](n: BigInt, list: List[T]): List[T] = {
  //  require(n >= 0)
  //  decreases(n)
  //  if (n == 0) Nil()
  //  else {
  //    list match {
  //      case Cons(head, tail) => Cons(head, takeList(n - 1, tail))
  //      case Nil()            => Nil()
  //    }
  //  }
  //}.ensuring(res =>
  //  (n <= list.size && res.size == n) || (n > list.size && res.size == list.size)
  //)
/*
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
  }.ensuring(res =>
    (index >= 0 && index < A.size) || ((index < 0 || index >= A.size) && res == 0)
  )

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
    res == 0 || (i <= t && i < A.size && res == indexTo(A(i), t - i))
  )

  def y_in(
      t: BigInt
  )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
    if (i > 0 && t > 0) {
      // yout_lemma(t - 1)(i - 1)(A, x)
      y_out(t - 1)(i - 1)(A, x)
    } else BigInt(0)
  }.ensuring(res => res == indexTo(matmul(A, x, i), t - i) || i <= 0 || t <= 0)

  def y_out(
      t: BigInt
  )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
    y_in(t)(i)(A, x) + a_in(t)(i)(A) * w_in(t)(i)(x)
  }

  

  // def yout_lemma(
  //     t: BigInt
  // )(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
  //   require(t >= 0 && i >= 0 && matrixSizeCheck(A, x))
  //   decreases(i)
  //   val yout_res = y_out(t)(i)(A, x)

  //   if (t < i) {
  //     check(y_in(t)(i)(A, x) == 0)
  //     check(a_in(t)(i)(A) == 0)
  //     check(yout_res == 0)
  //   } else {
  //     A match {
  //       case Nil() => check(yout_res == 0)
  //       case Cons(head, tail) => {
  //         // yout_lemma(t)(i-1)(A, x)
  //         if(t < i + head.size) {

  //         }
  //         else {
  //           check(yout_res == 0)
  //         }
  //       }
  //     }
  //   }
  // }.ensuring(y_out(t)(i)(A, x) == indexTo(matmul(A, x, i+1),t - i))

  def output(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && matrixSizeCheck(A, x))
    y_in(t)(x.size)(A, x)
  }

  def outputSpec(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && A.size >= 0 && matrixSizeCheck(A, x))

    val res = matmul(A, x, x.size)

    if (t < x.size) 0
    else if (t - x.size < res.size) {
      indexTo(res, t - x.size)
    } else 0
  }

  def verifyOutput(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(t >= 0 && A.size >= 0 && matrixSizeCheck(A, x))

    val res = matmul(A, x, x.size)
    if (t < x.size) {
      assert(true)
    } else if (t - x.size < res.size) {
      check(t > 0 && x.size > 0)
      check(indexTo(res, t - x.size) == y_in(t)(x.size)(A, x))
    } else {
      check(x.size >= A.size)
      check(a_in(t)(x.size)(A) == 0)
      // possibly tricky part of the proof requiring induction
      // need to prove that the systolic array stays outputting 0
      // since i decreases with t in y_in, the t >= x.size + res.size should be an invariant
      check(y_in(t)(x.size)(A, x) == 0)
    }
  }.ensuring(output(t)(A, x) == outputSpec(t)(A, x))*/

  def main(args: Array[String]): Unit = {
    // 1 3    5
    // 2 4    6
    // val A = List[List[BigInt]](List[BigInt](1,4,7),List[BigInt](2,5,8),List[BigInt](3,6,9))
    // val x = List[BigInt](1,2,3)
    // val n = BigInt("3")
    // for (t <- 0 until 10) {
    //  for (i <- 0 until 3) {
    //    printf("yout(t=%d,i=%d)=%d, ref = %d \n", t, i, y_out(BigInt(t))(BigInt(i))(A,x),  indexTo(matmul(A, x, i+1),t - i))
    //  }
    // }
    // println(matmul(A,x,n))
    // println(matmul(A.take(n), x.take(n), n))
    // println(matmul(A, x, n))
    // lemma1(A,x,n)
//
    // println(matmul(A, x, 0))
    // println(emv(x.head, A.head))

    // println(matmul(A, x).toString())

    // print("Expected\tGot\n")
    // for (t <- 0 until 10) {
    //   printf("%d\t\t%d\n", output(t)(A, x), outputSpec(t)(A, x))
    // }
  }
}
