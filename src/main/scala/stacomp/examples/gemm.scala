package stacomp.examples

import stacomp.*
import stacomp.TimeVal.*

object gemm {
  def main(args: Array[String]): Unit = {
    // Systolic array specs
    val i = SysIndex("i")
    val j = SysIndex("j")

    val A = InputArray(2, "A")
    val B = InputArray(2, "B")

    val a_in = CellPort("a_in")
    val a_out = CellPort("a_out")
    val b_in = CellPort("b_in")
    val b_out = CellPort("b_out")
    val y_in = CellPort("y_in")
    val y_out = CellPort("y_out")

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
        List(y_out -> (y_in + a_in * b_in),
        a_out -> a_in,
        b_out -> b_in)
      ),
      ConnSpec(
        List(y_in -> DelayedSelfCellConnection(y_out),
        a_in -> DelayedPreviousCellConnection(j, a_out, A_in),
        b_in -> DelayedPreviousCellConnection(i, b_out, B_in))
      )
    )

    val content = s.compileStainless()
    java.nio.file.Files.write(java.nio.file.Paths.get(args(1)), content.getBytes)
  }
}
