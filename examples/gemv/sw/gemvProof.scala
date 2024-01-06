//> using scala "3.2.0"
//> using jar "../../../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

import gemvImpl.*
import gemvRef.*

object gemvProof {
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
    decreases(A.size)

    (A, B) match {
      case (Cons(a, aa), Cons(b, bb)) =>
        assert(a + b == b + a)
        addVectorCommutativity(aa, bb)
      case (Nil(), Nil()) => assert(true)
    }

  }.ensuring(addVector(A, B) == addVector(B, A))

  ////////////////////
  // MATMUL LEMMAS //
  //////////////////

  def emvLinearityLemma(
      A: List[BigInt],
      x: BigInt,
      i: BigInt
  ): Unit = {
    require(i >= 0 && i < A.size)
    if (i == 0) {
      assert(emv(x, A).head == x * A.head)
    } else {
      A match {
        case Cons(a, Nil()) => {
          assert(A(i) == a)
        }
        case Cons(a, aa) => {
          emvLinearityLemma(aa, x, i - 1)
          assert(emv(x, aa)(i - 1) == x * aa(i - 1))
          assert(emv(x, A) == Cons(x * a, emv(x, aa)))
          assert(aa(i - 1) == A(i))
          assert(emv(x, A)(i) == emv(x, aa)(i - 1))
        }
      }
    }
  }.ensuring(emv(x, A)(i) == x * A(i))

  def addVectorLinearityLemma(
      A: List[BigInt],
      B: List[BigInt],
      i: BigInt
  ): Unit = {
    require(i >= 0 && i < A.size && A.size == B.size)
    if (i == 0) {
      assert(addVector(A, B).head == A.head + B.head)
    } else {
      (A, B) match {
        case (Cons(a, Nil()), Cons(b, Nil())) => {
          assert(A(i) == a)
          assert(B(i) == b)
        }
        case (Cons(a, aa), Cons(b, bb)) => {
          addVectorLinearityLemma(aa, bb, i - 1)
          assert(addVector(aa, bb)(i - 1) == aa(i - 1) + bb(i - 1))
          assert(addVector(A, B) == Cons(a + b, addVector(aa, bb)))
          assert(aa(i - 1) == A(i))
          assert(bb(i - 1) == B(i))
          assert(addVector(A, B)(i) == addVector(aa, bb)(i - 1))
        }
      }
    }
  }.ensuring(addVector(A, B)(i) == A(i) + B(i))

  def takePreserveRectangularityLemma(
      A: List[List[BigInt]],
      n: BigInt
  ): Unit = {
    require(isRectangular(A) && n >= 0)
    A match {
      case Cons(head, tail) => {
        if (n > 0) {
          // check(lemma3(A, n))
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
    require(A.size >= 0 && X.size >= 0 && inputArraysCheck(A, X) && gas >= 0)
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
    require(A.size >= 0 && X.size >= 0 && inputArraysCheck(A, X))
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
          assert(matmul(A, X, A.size) == addVector(emv(x, a), matmul(aa, xx, A.size - 1)))
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
    require(A.size >= 0 && X.size >= 0 && inputArraysCheck(A, X) && gas >= 0)
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
          assert(addVector(emv(x, a), addVector(matmul(aa, xx, gas - 1), emv(xn, an))) == addVector(emv(x, a), matmul(aa :+ an, xx :+ xn, gas - 1)))
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
    require(A.size > 0 && x.size > 0 && inputArraysCheck(A, x))

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

  def matmulLinearityLemma(j: BigInt)(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(i > 0 && i < A.size)
    require(j >= 0 && j < A.head.size) // correct?
    require(A.size > 0 && x.size > 0 && inputArraysCheck(A, x))

    matmulAddRowLemma(i)(A, x)
    assert(addVector(matmul(A, x, i), emv(x(i), A(i)))(j) == matmul(A, x, i + 1)(j))
    addVectorLinearityLemma(matmul(A, x, i), emv(x(i), A(i)), j)
    assert(matmul(A, x, i)(j) == indexTo(matmul(A, x, i), j))
    emvLinearityLemma(A(i), x(i), j)
    assert(A(i)(j) == indexTo(A(i), j))
  }.ensuring(indexTo(matmul(A, x, i), j) + indexTo(A(i), j) * x(i) == indexTo(matmul(A, x, i + 1), j))

  ///////////////////////////////////////
  // SYSTOLIC ARRAY CORRECTNESS PROOF //
  /////////////////////////////////////

  def yin_lemma(t: BigInt)(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(t >= 0 && i >= 0 && inputArraysCheck(A, x))
    if (i == 0) {
      assert(true)
    } else {
      if (t <= 0) {
        assert(true)
      } else {
        yout_lemma(t - 1)(i - 1)(A, x)
      }
    }
  }.ensuring(y_in(t)(i)(A, x) == indexTo(matmul(A, x, i), t - i) || i <= 0 || t <= 0)

  def yout_lemma(t: BigInt)(i: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(t >= 0 && i >= 0 && inputArraysCheck(A, x))
    decreases(i)
    val yout_res = y_out(t)(i)(A, x)

    A match {
      case Nil() => {
        if (i == 0 || t == 0) {
          check(y_in(t)(i)(A, x) == 0)
        } else {
          yout_lemma(t - 1)(i - 1)(A, x)
          check(y_in(t)(i)(A, x) == 0)
        }
        check(a_in(t)(i)(A,x) == 0)
        check(yout_res == 0)
      }
      case Cons(head, tail) => {
        if (i == 0) {
          if (t >= A(0).size) {
            check(y_in(t)(i)(A, x) == 0)
            check(a_in(t)(i)(A,x) == 0)
            check(y_out(t)(i)(A, x) == 0)
          } else {
            check(y_in(t)(i)(A, x) == 0)
            check(a_in(t)(i)(A,x) == indexTo(A(0), t))
            check(matmul(A, x, i + 1) == emv(x(i), A(i)))
            emvLinearityLemma(A(i), x(i), t)
            check(y_out(t)(i)(A, x) == a_in(t)(i)(A,x) * w_in(t)(i)(A,x))
          }
        } else if (t < i) {
          check(a_in(t)(i)(A,x) == 0)
          if (t == 0) {
            check(y_in(t)(i)(A, x) == 0)
            check(yout_res == 0)
          } else {
            yout_lemma(t - 1)(i - 1)(A, x)
            assert(indexTo(matmul(A, x, i), t - i) == 0)
            check(y_in(t)(i)(A, x) == 0)
            check(yout_res == 0)
          }
        } else {
          (t < i + head.size, i < A.size) match {
            case (true, true) => {
              yout_lemma(t - 1)(i - 1)(A, x)
              check(y_out(t)(i)(A, x) == y_out(t - 1)(i - 1)(A, x) + a_in(t)(i)(A,x) * w_in(t)(i)(A,x))

              // By inductive hypothesis
              check(y_out(t)(i)(A, x) == indexTo(matmul(A, x, i), t - i) + a_in(t)(i)(A,x) * w_in(t)(i)(A,x))
              assert(i < A.size && i <= t)
              check(a_in(t)(i)(A,x) == indexTo(A(i), t - i))
              check(w_in(t)(i)(A,x) == indexTo(x, i))

              // By postcondition of a_in, w_in
              check(y_out(t)(i)(A, x) == indexTo(matmul(A, x, i), t - i) + indexTo(A(i), t - i) * indexTo(x, i))
              check(indexTo(x, i) == x(i))

              // t - i should be in range by if statement above
              /*check(indexTo(matmul(A, x, i),t - i) + indexTo(A(i), t - i) * indexTo(x, i)
               == matmul(A, x, i)(t - i) + A(i)(t - i) * x(i))*/
              assert(t - i < A.head.size)
              assert(t - i >= 0)
              matmulLinearityLemma(t - i)(i)(A, x)
            }
            case (false, true) => { // t-i >= head.size && i < A.size
              yout_lemma(t - 1)(i - 1)(A, x)
              rectangularIndexLemma(A, i)
              assert(a_in(t)(i)(A,x) == 0)
              assert(y_out(t - 1)(i - 1)(A, x) == 0)
              check(yout_res == 0)
            }
            case (_, false) => {
              // skewed
              yout_lemma(t - 1)(i - 1)(A, x)
              // y_out(t-1)(i-1)(A, x) == indexTo(matmul(A, x, i), t - i)
              assert(y_out(t)(i)(A, x) == y_out(t - 1)(i - 1)(A, x) + a_in(t)(i)(A,x) * w_in(t)(i)(A,x))
              assert(i >= A.size)
              assert(a_in(t)(i)(A,x) == 0)
              assert(y_out(t)(i)(A, x) == y_out(t - 1)(i - 1)(A, x))
              // indexTo(matmul(A, x, i+1), t - i) == indexTo(matmul(A, x, i), t - i)
              matmulGasLimitingLemma(A, x, i + 1)
              matmulGasLimitingLemma(A, x, i)
              // => assert(indexTo(matmul(A, x, i + 1), t - i) == indexTo(matmul(A, x, i), t - i))
            }
          }
        }
      }
    }
  }.ensuring(y_out(t)(i)(A, x) == indexTo(matmul(A, x, i + 1), t - i))

  def output(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && inputArraysCheck(A, x))
    y_in(t)(x.size)(A, x)
  }

  def outputSpec(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): BigInt = {
    require(t >= 0 && A.size >= 0 && inputArraysCheck(A, x))

    val res = matmul(A, x, x.size)

    if (t < x.size) 0
    else if (t - x.size < res.size) indexTo(res, t - x.size)
    else 0
  }

  def verifyOutput(t: BigInt)(A: List[List[BigInt]], x: List[BigInt]): Unit = {
    require(t >= 0 && A.size >= 0 && inputArraysCheck(A, x))

    yin_lemma(t)(x.size)(A, x)
  }.ensuring(output(t)(A, x) == outputSpec(t)(A, x))

}
