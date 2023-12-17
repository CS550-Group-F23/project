//> using scala "3.2.0"
//> using jar "../../../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object Gemv {
  
  //////////////////////////////////////
  // GENERIC LIST HELPERS/PROPERTIES //
  ////////////////////////////////////

  def partitionListLemma[T](A: List[T], n: BigInt): Unit = {
    require(n < A.size && n >= 0)
    if (n == 0) {
      assert(A.take(n) == Nil[T]())
      assert(A.drop(n) == A)
    } else {
      A match {
        case Nil[T]() => assert(true)
        case Cons(a, aa) => {
          partitionListLemma(aa, n - 1)
          check(A.take(n) == Cons(a, aa.take(n - 1)))
        }
      }
    }
  }.ensuring(A == (A.take(n) ++ A.drop(n)))

  def dropIndexLemma[T](A: List[T], n: BigInt): Unit = {
    require(n < A.size && n >= 0)

    if (n == 0) {
      assert(A.drop(n) == A)
      assert(A.take(1).head == A(0))
    } else {
      A match {
        case Nil[T]() => { assert(true) }
        case Cons(a, aa) => {
          dropIndexLemma(aa, n - 1)
          check(A.drop(n) == aa.drop(n - 1))
          check(aa(n - 1) == A(n))
        }
      }
    }
  }.ensuring(A.drop(n).take(1).head == A(n))

  def takeAppendLemma[T](A: List[T], n: BigInt): Unit = {
    require(n < A.size && n >= 0)
    partitionListLemma(A, n)
    ListSpecs.appendTakeDrop(A.take(n), A.drop(n), n + 1)
    check(A.take(n + 1) == A.take(n) ++ A.drop(n).take(1))
    dropIndexLemma(A, n)
  }.ensuring(A.take(n) :+ A(n) == A.take(n + 1))

  //////////////////////////////////////
  // MATMUL REFERENCE IMPLEMENTATION //
  ////////////////////////////////////

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

  def addVectorAssoc(
      A: List[BigInt],
      B: List[BigInt],
      C: List[BigInt]
  ): Unit = {
    require(A.size == B.size && B.size == C.size)

    (A, B, C) match {
      case (Cons(a, aa), Cons(b, bb), Cons(c, cc)) =>
        assert((a + b) + c == a + (b + c))
        addVectorAssoc(aa, bb, cc)
      case (Nil(), Nil(), Nil()) => assert(true)
    }

  }.ensuring(addVector(addVector(A, B), C) == addVector(A, addVector(B, C)))

  def addVectorCommutativity(A: List[BigInt], B: List[BigInt]): Unit = {
    require(A.size == B.size)

    (A, B) match {
      case (Cons(a, aa), Cons(b, bb)) =>
        assert(a + b == b + a)
        addVectorCommutativity(aa, bb)
      case (Nil(), Nil()) => assert(true)
    }

  }.ensuring(addVector(A, B) == addVector(B, A))

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

  ////////////////////
  // MATMUL LEMMAS //
  //////////////////

  def emvLinearityLemma(
    A: List[BigInt],
    x: BigInt,
    i: BigInt
  ): Unit = {
    require(i >= 0 && i < A.size)
    // TODO
    /*if (i == 0) {
      check(emv(x,A).head == A.head)
    } else {
      A match {
        case Nil() => {
          assert(true)
        }
        case Cons(a, aa) => {
          emvLinearityLemma(aa, x, i-1)    
        }
      }
    }*/
  }.ensuring(emv(x, A)(i) == x * A(i))

  def addVectorLinearityLemma(
    A: List[BigInt],
    B: List[BigInt],
    i: BigInt
  ): Unit = {
    require(i >= 0 && i < A.size && A.size == B.size)
    // TODO
  }.ensuring(addVector(A, B)(i) == A(i) + B(i))

  def takePreserveRectangularityLemma(
      A: List[List[BigInt]],
      n: BigInt
  ): Unit = {
    require(isRectangular(A) && n >= 0)
    A match {
      case Cons(head, tail) => {
        if (n > 0) {
          //check(lemma3(A, n))
          check(A.head == A.take(n).head)
          check(A.head.size == A.take(n).head.size)
          takePreserveRectangularityLemma(tail, n - 1)
        } else {
          check(A.take(n) == Nil())
        }
      }
      case Nil() => check(A.take(n) == Nil())
    }
  }.ensuring(isRectangular(A.take(n)))

  def rectangularIndexLemma(A: List[List[BigInt]], i: BigInt): Unit = {
    require(A.size >= 0 && isRectangular(A))
    require(i >= 0 && i < A.size)

    if (i == 0) {
      assert(true)
    } else {
      A match {
        case Nil() => { assert(true) }
        case Cons(a, aa) => {
          rectangularIndexLemma(aa, i - 1)
        }
      }
    }
  }.ensuring(A.size == 0 || (A.head.size == A(i).size))

  def matmulTakeGasEquivalenceLemma(
      A: List[List[BigInt]],
      X: List[BigInt],
      gas: BigInt
  ): Unit = {
    require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X) && gas >= 0)
    decreases(gas)

    check(A.take(gas).size == X.take(gas).size)
    takePreserveRectangularityLemma(A, gas)
    val a = matmul(A.take(gas), X.take(gas), gas)
    val b = matmul(A, X, gas)

    if (gas > 0) {
      (A, X) match {
        case (Cons(h1, t1), Cons(h2, t2)) => {
          matmulTakeGasEquivalenceLemma(t1, t2, gas - 1)
          if (t2.size == 0 || gas == 1) {
            check(b == emv(X.head, A.head))
          } else {
            check(addVector(emv(h2, h1), matmul(t1, t2, gas - 1)) == b)
          }
        }
        case (Nil(), Nil()) => {
          assert(A.take(gas) == Nil())
          assert(X.take(gas) == Nil())
          assert(b == Nil())
        }
      }
    } else {
      assert(matmul(A, X, gas) == Nil())
    }

  }.ensuring(matmul(A.take(gas), X.take(gas), gas) == matmul(A, X, gas))

  def matmulGasLimitingLemma(
      A: List[List[BigInt]],
      X: List[BigInt],
      gas: BigInt
  ): Unit = {
    require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X))
    require(gas >= A.size)
    (A, X) match {
      case (Nil(), Nil()) => {
        assert(matmul(A, X, gas) == Nil())
      }
      case (Cons(a, aa), Cons(x, xx)) => {
        if (aa.size == 0 || gas == 1) {
          check(true)
        } else {
          matmulGasLimitingLemma(aa, xx, gas - 1)
          assert(matmul(A, X, A.size) == addVector(emv(x, a),matmul(aa, xx, A.size - 1)))
          assert(matmul(A, X, gas) == addVector(emv(x, a), matmul(aa, xx, gas - 1)))
        }
      }
    }
  }.ensuring(matmul(A, X, A.size) == matmul(A, X, gas))

  def matmulAppendRowLemma(
      A: List[List[BigInt]],
      X: List[BigInt],
      gas: BigInt,
      an: List[BigInt],
      xn: BigInt
  ): Unit = {
    require(A.size >= 0 && X.size >= 0 && matrixSizeCheck(A, X) && gas >= 0)
    require(A.size == 0 || A.head.size == an.size)
    require(gas > A.size)

    (A, X) match {
      case (Nil(), Nil()) => assert(true)
      case (Cons(a, aa), Cons(x, xx)) => {
        if (aa.size == 0 || gas == 1) assert(true)
        else {
          // addVector(matmul(aa, xx, gas),emv(xn, an)) == matmul(aa :+ an, xx :+ xn, n)
          matmulAppendRowLemma(aa, xx, gas - 1, an, xn)
          // Add emv(x,a) to both sides
          assert(addVector(emv(x, a),addVector(matmul(aa, xx, gas - 1), emv(xn, an))) == addVector(emv(x, a), matmul(aa :+ an, xx :+ xn, gas - 1)))
          // Associate LHS
          addVectorAssoc(emv(x, a), matmul(aa, xx, gas - 1), emv(xn, an))
          assert(addVector(emv(x, a), matmul(aa, xx, gas - 1)) == matmul(A, X, gas))
          assert(addVector(emv(x, a), matmul(aa :+ an, xx :+ xn, gas - 1)) == matmul(A :+ an, X :+ xn, gas))
        }
      }
    }
  }.ensuring((A.size == 0 && X.size == 0) || addVector(matmul(A, X, gas), emv(xn, an)) == matmul(A :+ an, X :+ xn, gas))

  def matmulAddRowLemma(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(i > 0 && i < A.size)
    require(A.size > 0 && x.size > 0 && matrixSizeCheck(A, x))

    // 1. Taking the first i elements is equivalent if the gas is i.
    // matmul(A,x,i) == matmul(A.take(i), x.take(i), i)
    matmulTakeGasEquivalenceLemma(A, x, i)

    // 2. This is also equal to i+1 as gas because A.take(i) is of size i.
    // matmul(A.take(i), x.take(i), i) == matmul(A.take(i), x.take(i), i+1)
    matmulGasLimitingLemma(A.take(i), x.take(i), i + 1)

    // 3. Adding emv(x(i), A(i)) to the matmul result is the same as appending it to the array.
    // addVector(matmul(A.take(i),X.take(i),i+1),emv(x(i), A(i)) == matmul(A.take(i) :+ A(i), X.take(i) :+ X(i), i+1)
    takePreserveRectangularityLemma(A, i) // } Needed for precondition of matmulAppendRow
    rectangularIndexLemma(A, i)
    matmulAppendRowLemma(A.take(i), x.take(i), i + 1, A(i), x(i))

    // 4. A.take(i) :+ A(i) == A.take(i+1), likewise for x
    takeAppendLemma(A, i)
    takeAppendLemma(x, i)

    // Check that 3 & 4 have been put together successfully.
    check(addVector(matmul(A.take(i), x.take(i), i + 1), emv(x(i), A(i))) == matmul(A.take(i + 1), x.take(i + 1), i + 1))

    // 5. Same as the first step, but in reverse and for i+1.
    // matmul(A.take(i+1), x.take(i+1), i+1) == matmul(A,x,i+1)
    takePreserveRectangularityLemma(A, i + 1) // have to remind stainless that A.take(i+1) is also rectangular
    matmulTakeGasEquivalenceLemma(A, x, i + 1)
  }.ensuring(addVector(matmul(A, x, i), emv(x(i), A(i))) == matmul(A, x, i + 1))

  // TODO - go back to top down and come back to this when we have a better idea of the edge cases
  /*def matmulLinearityLemma(j: BigInt)(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(i > 0 && i < A.size)
    require(i > 0 && i < A.size)
    require(A.size > 0 && x.size > 0 && matrixSizeCheck(A, x))
       
  }.ensuring(indexOf(matmul(A, x, i), j) + indexOf(A(i), j) * x(i) == indexOf(matmul(A, x, i + 1), j))*/


  ////////////////////////////////////
  // SYSTOLIC ARRAY IMPLEMENTATION //
  //////////////////////////////////

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

  def output(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && matrixSizeCheck(A, x))
    y_in(t)(x.size)(A, x)
  }

  ///////////////////////////////////////
  // SYSTOLIC ARRAY CORRECTNESS PROOF //
  /////////////////////////////////////

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
  }.ensuring(output(t)(A, x) == outputSpec(t)(A, x))

  //////////////////
  // TEST DRIVER //
  ////////////////

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
