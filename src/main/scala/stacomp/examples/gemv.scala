package stacomp.examples

import stacomp.*
import stacomp.TimeVal.*

object gemv {
  def main(args: Array[String]): Unit = {
    // Systolic array specs
    val i = SysIndex("i")
    val A = InputArray(2, "A")
    val W = InputArray(1, "W")

    // sval a_in = CellPort("a_in")
    // val w_in = CellPort("w_in")
    val y_in = CellPort("y_in")
    val y_out = CellPort("y_out")

    val a_in = SysPort(
      name = "a_in",
      schedule = Schedule((Until(i), DontCare), (Until(i + A(i).size), A(i)(T - i)), (Henceforth, 0.E)),
      indexConstraints = List(A.size > 0.E, i < A.size),
      defaultValue = 0.E
    )
    val w_in = SysPort(
      name = "w_in",
      schedule = Schedule((Henceforth, W(i))),
      indexConstraints = List(i < W.size),
      defaultValue = 0.E
    )

    val s = SystolicSpec(
      SystemSpec("gemv", List(i), List(A, W)),
      InputSpec(
        List(a_in, w_in)
      ),
      CellSpec(
        List(a_in, w_in, y_in),
        List((y_out, MACExpr(y_in, a_in, w_in)))
      )
    )

    val content = s.compileStainless()
    java.nio.file.Files.write(java.nio.file.Paths.get(args(1)), content.getBytes)
  }
}
