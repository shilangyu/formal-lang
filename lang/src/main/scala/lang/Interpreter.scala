package lang

import lang.Name
import lang.Expr.*
import lang.Stmt.*
import lang.State

class UndeclaredVariableException() extends Exception()
class InvalidLocException() extends Exception()

object Interpreter {

  def evalExpr(expr: Expr, state: State): Boolean = expr match {
    case True       => true
    case False      => false
    case Nand(l, r) => !(evalExpr(l, state) && evalExpr(r, state))
    case Ident(n)   => 
      val locOption = state(0).head.get(n)
      locOption match {
        case Some(loc) => 
          val vOption = state(1).get(loc)
          vOption match {
            case Some(v) => v
            case None    => throw new InvalidLocException
          }
        case None      => throw new UndeclaredVariableException
      }
    //case Expr.Ref(e)     => isExprClosed(e, env)
    //case Expr.Deref(e)   => isExprClosed(e, env)
  }//.ensuring(_ => isExprClosed(expr, state(0).head))

}
