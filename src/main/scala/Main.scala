import scala.collection.mutable
object Project {
    trait Compilable {
        def visit(sb: StringBuilder): Unit
    }

    case class FunctionSpec (
    )

    case class SystolicSpec (
        name: String,
        inputSpec: FunctionSpec,
        behavioralSpec: FunctionSpec,
        structuralSpec: FunctionSpec,
        outputSpec: FunctionSpec
    ) extends Compilable  {
        def visit(sb: StringBuilder): Unit = {
            sb ++= s"object $name {\n"
            // Fill in the rest of the fucking compiler
            sb ++= s"}"
        }
    }

    
    def main(args: Array[String]): Unit = {
        val s = SystolicSpec(
            "Gemv",
            FunctionSpec(),
            FunctionSpec(),
            FunctionSpec(),
            FunctionSpec(),
        )
        val sb = mutable.StringBuilder()
        s.visit(sb)
        println(sb.toString())
    }
}