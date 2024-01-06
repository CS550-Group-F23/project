package stacomp

trait Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit
    def -(that: Expr): Expr = MinusExpr(this, that)
    def +(that: Expr): Expr = PlusExpr(this, that)
    def *(that: Expr): Expr = MulExpr(this, that)
    def <(that: Expr): IndConstraint = IndConstraint.Lt(this, that)
    def >(that: Expr): IndConstraint = IndConstraint.Lt(that, this)
    def <=(that: Expr): IndConstraint = IndConstraint.Leq(this, that)
    def >=(that: Expr): IndConstraint = IndConstraint.Leq(that, this)
    def ==(that: Expr): IndConstraint = IndConstraint.Eq(this, that)
}

case class IntLitExpr(
    i: Int
) extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = sb ++= s"$i"
}

case class IntSymExpr(
    sym: String
) extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = sb ++= sym
}

extension (i: Int) {
    def E: Expr = IntLitExpr(i)
}

case object T extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = sb ++= "t"
}

case class MinusExpr(
    e1: Expr,
    e2: Expr
) extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = {
        e1.visit(sb, sspec)
        sb ++= "-"
        e2.visit(sb, sspec)
    }
}

case class PlusExpr(
    e1: Expr,
    e2: Expr
) extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = {
        e1.visit(sb, sspec)
        sb ++= "+"
        e2.visit(sb, sspec)
    }
}

case class MulExpr(
    e1: Expr,
    e2: Expr
) extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = {
        e1.visit(sb, sspec)
        sb ++= "*"
        e2.visit(sb, sspec)
    }
}

case class ArraySizeExpr(
    dims: Int,
    name: String,
    inds: List[Expr]
) extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = {
        sb ++= s"$name"
        inds.map(ind => {
            sb ++= "("
            ind.visit(sb, sspec)
            sb ++= ")"
        })
        sb ++= ".size"
    }
}

case object DontCare extends Expr {
    def visit(sb: StringBuilder, sspec: SystemSpec): Unit = sb ++= "0"
}