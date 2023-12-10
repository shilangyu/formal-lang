package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*


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

  def closedStmtEvaluates(stmt: Stmt, state: State): Unit = {
    require(Checker.isStmtClosed(stmt, state._1)._1)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isExprClosed(value, state._1))
        closedExprEvaluates(value, state)
      case Assign(to, value) =>
        assert(state._1.contains(to))
        assert(Checker.isExprClosed(value, state._1))
        closedExprEvaluates(value, state)
      case If(cond, body) =>
        assert(Checker.isExprClosed(cond, state._1))
        closedExprEvaluates(cond, state)
        closedStmtEvaluates(body, state)
      //case While(cond, body) => ()state, ??
      case Seq(s1, s2) =>
        assert(Checker.isStmtClosed(s1, state._1)._1)
        closedStmtEvaluates(s1, state)
        val menv = Checker.isStmtClosed(s1, state._1)._2
        assert(Checker.isStmtClosed(s2, menv)._1)
        closedStmtEvaluates(s2, (menv, state._2, state._3))
  }.ensuring( fstate =>
    Interpreter.evalStmt(stmt, state) match
      case Right(s) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )
}