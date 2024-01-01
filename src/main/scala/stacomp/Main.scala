package stacomp

object Project {
    trait Compilable {
        def visit(sb: StringBuilder): Unit
    }

    type FunctionSpec = List[(TimeSym, Expr)]

    def 

    case class CellSpec (

    )

    case class StructureSpec (

    )

    case class SystolicSpec (
        name: String,
        inputSpec: FunctionSpec,
        cellSpec: FunctionSpec,
        structureSpec: FunctionSpec,
        outputSpec: FunctionSpec
    ) extends Compilable  {
        def visit(sb: StringBuilder): Unit = {
            sb ++= s"object $name {\n"
            // Fill in the rest of the fucking compiler
            sb ++= s"}"
        }
    }

}