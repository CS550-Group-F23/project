package stacomp.examples

import stacomp.Project.*
import scala.collection.mutable

object gemv {
    def main(args: Array[String]): Unit = {
        val A = InputArray(2, "A")
        val W = InputArray(1, "W")
        


        val s = SystolicSpec(
            "gemv",
            FunctionSpec(),
            FunctionSpec(),
            FunctionSpec(),
            FunctionSpec(),
        )
        val sb = mutable.StringBuilder()
        s.visit(sb)
        val content = sb.toString()
        java.nio.file.Files.write(java.nio.file.Paths.get(args(1)), content.getBytes)
    }
}