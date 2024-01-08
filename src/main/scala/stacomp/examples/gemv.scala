package stacomp.examples

import stacomp.*
import stacomp.TimeVal.*

object gemv {
  def main(args: Array[String]): Unit = {
    // Declare indices over the dimensions of the array.

    // In our case, i represents the single dimension we have.
    val i = SysIndex("i")


    // Declare input data to the systolic array.

    // Since this is matrix-vector multiplication, we take
    // a matrix (Dimensions: 2) A and a vector (Dimensions: 1) W
    val A = InputArray(2, "A")
    val W = InputArray(1, "W")


    // Declare all ports for an individual PE.

    // In our case, we take in the previous result in y_in port,
    // and output the result of the MAC in y_out.
    val y_in = CellPort("y_in")
    val y_out = CellPort("y_out")


    // Declare all system ports. These are ports where input data is being fed in.
    // In the STA spec, these are subjects we would access
    // with Out(_, S) where S is the systolic array.

    // We have two sources of input data: A and W.
    // Input port takes in a name, schedule, constraints, and default value.
    // Constraints are to verify we are accessing the system port at a place
    // that makes sense (e.g. what does it mean to access A outside its bounds?),
    // while the schedule describes how the values change over time.
    // The schedule is specified very similarly to the STA spec: on the left hand side
    // of every tuple here, we have a TimeVal object that can be either At, Until, or Henceforth.
    // T is implicit here; so here, we are essentially saying the port has DontCare until it reaches i,
    // and then A(i)(t-i) as long as it is less than i + A(i).size), and then 0 onwards.
    // Finally, the default value simply describes what the output should be when the index constraints are violated.
    val a_in = SysPort(
      name = "a_in",
      schedule = Schedule(
        Until(i) -> DontCare,
        Until(i + A(i).size) -> A(i)(T - i),
        Henceforth -> 0.E
      ),
      indexConstraints = List(A.size > 0.E, i < A.size),
      defaultValue = 0.E
    )
    // For w_in, we do not depend on time, so we just have a single henceforth, like the STA spec.
    // We call w_in a "port" even though in the original spec, it was modeled explicitly as memory.
    // w_in can still be generated to hardware as a register, since a_in would have to be a shift register as well.
    // In general, the abstraction of a SysPort translates nicely to a shift register.
    val w_in = SysPort(
      name = "w_in",
      schedule = Schedule(Henceforth -> W(i)),
      indexConstraints = List(i < W.size),
      defaultValue = 0.E
    )

    // Finally, we put everything together. A systolic array spec
    // is made up of System, Input, Cell, and Conn spec.
    // This is a slight deviation from the terms used in the paper, 
    // but they express most of the same concepts.
    val s = SystolicSpec(
      // System spec is just the parameters we defined earlier: indices, and input data.
      SystemSpec("gemv", List(i), List(A, W)),
      // Input Spec lists each of the system ports i.e. how the systolic array gets input data.
      InputSpec(
        List(a_in, w_in)
      ),
      // Cell Spec describes the behavior of each cell: Listing every input and output port of the cell.
      // For output ports, we must describe what (purely combinational!) expression is computed.
      CellSpec(
        // There is a bit of syntax sugar here, since we list a_in,w_in directly, while they are not technically 
        // a cell port, but rather a port on the array. Since they are connected directly however, the language 
        // just lets you express it like normal.
        List(a_in, w_in, y_in),
        // This syntax allows you to construct arbitrary math expressions from ports.
        // Normally this doesn't really make sense, since you need to evaluate ports at a given time and index,
        // but because we assume all cells to be purely combinational circuits, we know 
        // t and all the other indices stay the same.
        List(y_out -> (y_in + a_in * w_in))
      ),
      // Finally, the connection spec. 
      // This is a subset of what was called the structural spec in STA before.
      // We create a list of tuples for every input cell port that describes what other ports
      // they should be connected to. In the case of y_in, we have a delayed connection to every
      // previous cell. At the first cell, there is no previous cell, so we just feed it 0.
      // DelayedPreviousCellConnection expresses this concisely.
      // It is an example of a Connection object, which we have other examples for as well.
      ConnSpec(
        List(y_in -> DelayedPreviousCellConnection(i, y_out, ConstantPort(0)))
      )
    )

    val content = s.compileStainless()
    java.nio.file.Files.write(java.nio.file.Paths.get(args(1)), content.getBytes)
  }
}
