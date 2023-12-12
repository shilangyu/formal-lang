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

  def closedStmtEvaluates(stmt: Stmt, state: State): Unit = {
    val env = state._1
    require(Checker.isStmtClosed(stmt, env)._1)
    stmt match
      case Decl(name, value) =>
        closedExprEvaluates(value, state)
      case Assign(to, value) =>
        closedExprEvaluates(value, state)
        assert(state._1.contains(to))
      case If(cond, body) =>
        assert(Checker.isExprClosed(cond, env))
        closedExprEvaluates(cond, state)
      case Seq(s1, _) =>
        closedStmtEvaluates(s1, state)
  }.ensuring(
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  def test(stmt: Stmt, state: State): Unit = {
    require(Interpreter.evalStmt(stmt, state).isRight)
    val newState = Interpreter.evalStmt(stmt, state)
  }.ensuring(Interpreter)
  */

  def locIncreases(stmt: Stmt, state: State): Unit = {
    decreases(stmt)

    stmt match
      case Decl(_, _)   =>
        Interpreter.traceStmt1(Cmd(stmt, state)) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(newState) =>
              assert(newState._3 == state._3 + 1)
            case _ => ()
      case Seq(s1, _)   => 
        locIncreases(s1, state)
      case _            => ()

  }.ensuring(
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(newState) => newState._3 >= state._3
/*
          if stmt.isInstanceOf[Decl] then newState._3 == state._3 + 1
          else newState._3 == state._3
          */
        case Cmd(_, newState) => newState._3 >= state._3
    )

  /*
  def noDoubleLoc(stmt: Stmt, state: State): Unit = {
    //require(Interpreter.traceStmt1(stmt, state).isRight) 
    decreases(stmt)
    val mem = state._2
    val freeLoc = state._3
    require(!mem.contains(freeLoc))

    locIncreases(stmt, state)
    stmt match
      case Decl(name, value)  =>
        Interpreter.traceStmt1(Cmd(stmt, state)) match
        //assert(newState._3 == freeLoc+1)
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(newState) => 
              assert(newState._2.contains(state._3))
            case Cmd(_, newState) => ()
      case Seq(s1, _)        => 
        noDoubleLoc(s1, state)
      case _ => ()
  }.ensuring(
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(newState) => 
          newState._2 == state._2 || newState._2 - state._3 == state._2
        case Cmd(_, newState) => 
          newState._2 == state._2 || newState._2 - state._3 == state._2
    )
  */

}
