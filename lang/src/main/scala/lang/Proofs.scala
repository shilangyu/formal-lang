package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*


object Proofs {

  def closedExprEvaluates(expr: Expr, state: State): Unit = {
    require(Checker.isExprClosed(expr, state._1))

    expr match
      case True => ()
      case False => ()
      case Nand(left, right) =>
        assert(Checker.isExprClosed(left, state._1))
        assert(Checker.isExprClosed(right, state._1))
        closedExprEvaluates(left, state)
        closedExprEvaluates(right, state)
      case Ident(name) =>
        assert(state._1.contains(name))
        ()
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  //def closedStmtEvalua

}