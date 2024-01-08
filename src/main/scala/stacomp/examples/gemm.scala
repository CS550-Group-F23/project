package stacomp.examples

import stacomp.*
import stacomp.TimeVal.*

object gemm {
  def main(args: Array[String]): Unit = {
    // We recommend reading the comments in gemv.scala first to 
    // explain the syntax of stacomp. The comments here will simply
    // discuss some of the changes required to express gemm.

    // We introduce 2 indices instead of one, 
    // since we have a grid of cells now.
    val i = SysIndex("i")
    val j = SysIndex("j")

    // Both inputs are 2D arrays.
    val A = InputArray(2, "A")
    val B = InputArray(2, "B")

    // Every cell takes in the A input, and forwards it to the next on one axis.
    // It also takes in the B input, and forwards it directly on the other.
    // Since this is an output stationary array, the cell also has a register
    //  which it uses to accumulate the result.
    // However, we can reuse our existing abstractions for this: a register can be modeled
    // as an input and output port, and in the connection spec, we can simply indicate that 
    // the output is delayed by one from the input.
    val a_in = CellPort("a_in")
    val a_out = CellPort("a_out")
    val b_in = CellPort("b_in")
    val b_out = CellPort("b_out")
    val y_in = CellPort("y_in")
    val y_out = CellPort("y_out")

    // System input ports look very similar to A_in for gemv except this time
    // we have 2 and we have different indices.
    val A_in = SysPort(
      name = "A_in",
      schedule = Schedule(
        Until(i) -> DontCare,
        Until(i + A(i).size) -> A(i)(T - i),
        Henceforth -> 0.E
      ),
      indexConstraints = List(A.size > 0.E, i < A.size),
      defaultValue = 0.E
    )

    val B_in = SysPort(
      name = "B_in",
      schedule = Schedule(
        Until(j) -> DontCare,
        Until(j + B(j).size) -> B(j)(T - j),
        Henceforth -> 0.E
      ),
      indexConstraints = List(B.size > 0.E, j < B.size),
      defaultValue = 0.E
    )

    val s = SystolicSpec(
      SystemSpec("gemm", List(i,j), List(A, B)),
      InputSpec(
        List(A_in, B_in)
      ),
      CellSpec(
        List(a_in, b_in, y_in),
        // Individual cell spec is the exact same.
        // Notice that this time though, y_out and y_in mean different things!
        // These are the ports for the cell's internal registers.
        List(y_out -> (y_in + a_in * b_in),
        // We must also forward the A and B input data directly.
        a_out -> a_in,
        b_out -> b_in)
      ),
      ConnSpec(
        // We introduce a new type of Connection here,
        // which essentially expresses that we want a register inside the cell itself,
        // instead of being in between cells (DelayedCellPreviousConnection).
        // This is key to making the output stationary array work.
        List(y_in -> DelayedSelfCellConnection(y_out),
        // Meanwhile, the other connections still work like the GEMV systolic array, 
        // being registers in between cells.
        a_in -> DelayedPreviousCellConnection(j, a_out, A_in),
        b_in -> DelayedPreviousCellConnection(i, b_out, B_in))
      )
    )

    val content = s.compileStainless()
    java.nio.file.Files.write(java.nio.file.Paths.get(args(1)), content.getBytes)
  }
}
