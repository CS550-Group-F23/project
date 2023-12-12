//> using scala "3.2.0"
//> using jar "../lib/stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import stainless.proof.check

object vecAddExample {
    def vecAdd(A: List[BigInt], B: List[BigInt], n: BigInt ): List[BigInt] = {
        require(n >= 0 && A.size == B.size)
        if (n > 0) {
            (A,B) match {
                case (Cons(a,aa),Cons(b,bb)) => Cons(a*b, vecAdd(aa,bb,n-1))
                case (Nil(),Nil()) => Nil()
            }
        } else {
            Nil()
        }
    }

    def lemma1(A: List[BigInt], B: List[BigInt], n: BigInt): Unit = {
        require(n >= 0 && A.size == B.size)

        if (n == 0)   {
            assert(true)           
        } else {
            (A,B) match {
                case (Cons(h1, t1), Cons(h2, t2)) => {
                    lemma1(t1, t2, n-1)
                }
                case (Nil(), Nil())               => {
                    assert(A.take(n) == Nil())
                    assert(B.take(n) == Nil())
                    assert(vecAdd(A,B,n) == Nil())
                }
            }
        }
    }.ensuring{vecAdd(A.take(n), B.take(n),n) == vecAdd(A,B,n).take(n)}
}