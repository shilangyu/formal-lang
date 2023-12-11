package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*
import Conf.*


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

  /*
  def closedStmtEvaluates(stmt: Stmt, state: State): Unit = {
    val env = state._1
    require(Checker.isStmtClosed(stmt, env)._1)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isExprClosed(value, env))
        closedExprEvaluates(value, state)
      case Assign(to, value) =>
        assert(state._1.contains(to))
        assert(Checker.isExprClosed(value, env))
        closedExprEvaluates(value, state)
      case If(cond, body) =>
        assert(Checker.isExprClosed(cond, env))
        closedExprEvaluates(cond, state)
        closedStmtEvaluates(body, state)
      //case While(cond, body) => ()state, ??
      case Seq(s1, s2) =>
        assert(Checker.isStmtClosed(s1, env)._1)
        closedStmtEvaluates(s1, state)
        //val menv = Checker.isStmtClosed(s1, env)._2
        //assert(Checker.isStmtClosed(s2, menv)._1)
        assert(Checker.isStmtClosed(s2, env)._1)
        //closedStmtEvaluates(s2, (menv, state._2, state._3))
        closedStmtEvaluates(s2, state)
  }.ensuring(
    Interpreter.evalStmt(stmt, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  def test(stmt: Stmt, state: State): Unit = {
    require(Interpreter.evalStmt(stmt, state).isRight)
    val newState = Interpreter.evalStmt(stmt, state)
  }.ensuring(Interpreter)

  def noLoc(stmt: Stmt, state: State): Unit = {
    require(Interpreter.evalStmt(stmt, state).isRight) 
    require(!state._2.contains(state._3))
    val freeLoc = state._3
    stmt match
      case Decl(name, value)  => 
        val Right(newState) = Interpreter.evalStmt(stmt, state)
        //assert(newState.isRight)
        assert(newState._3 == freeLoc+1)
        assert(newState._2.contains(freeLoc))
      case Assign(_,_)        => ()
      case If(_, body)        =>
        noLoc(body, state)
      case Seq(s1, s2)        => 
        noLoc(s1, state)
        val Right(newState) = Interpreter.evalStmt(stmt, state)
        noLoc(s2, newState)
  }
  */

  def locIncreases(stmt: Stmt, state: State): Unit = {
    require(Interpreter.traceStmt1(Cmd(stmt, state)).isRight)
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Left(_)  => ()
      case Right(St(newState)) => stmt match
        case Decl(_, _) => 
          assert(newState._3 == state._3 + 1)
        case _ => ()
      case Right(Cmd(_, newState)) => stmt match
        case Decl(_, _) => 
          assert(newState._3 == state._3 + 1)
        case Seq(s, _) => s match
          case Decl(_, _) =>
            assert(newState._3 == state._3 + 1)
          case _ => ()
        case _ => ()
  }.ensuring(
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Left(_)                  => true
      case Right(St(newState))      => newState._3 >= state._3
      case Right(Cmd(_, newState))  => newState._3 >= state._3
      )
}
