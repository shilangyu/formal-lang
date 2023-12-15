package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*
import Conf.*


object Proofs {

  def closedExprEvaluates(expr: Expr, state: State): Unit = {
    val env = state._1.head
    require(Checker.isExprClosed(expr, env))
    expr match
      case True => ()
      case False => ()
      case Nand(left, right) =>
        assert(Checker.isExprClosed(left, env))
        assert(Checker.isExprClosed(right, env))
        closedExprEvaluates(left, state)
        closedExprEvaluates(right, state)
      case Ident(name) =>
        assert(env.contains(name))
        ()
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  def closedStmtNoUndeclaredVar(stmt: Stmt, state: State): Unit = {
    val envs = state._1
    val env = envs.head
    require(Checker.isStmtClosed(stmt, envs)._1)
    stmt match
      case Decl(name, value) =>
        closedExprEvaluates(value, state)
      case Assign(to, value) =>
        closedExprEvaluates(value, state)
        assert(env.contains(to))
      case If(cond, body) =>
        assert(Checker.isExprClosed(cond, env))
        closedExprEvaluates(cond, state)
      case Seq(stmt1, _) =>
        closedStmtNoUndeclaredVar(stmt1, state)
      case Block(_, stmt1)            =>
        closedStmtNoUndeclaredVar(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )
  */

  /*
  def noRedeclStmtNoRedeclaredVar(stmt: Stmt, state: State): Unit = {
    val env = state._1
    require(Checker.noRedecl(stmt, env)._1)
    stmt match
      case Decl(name, value) =>
        assert(!state._1.contains(name))
      case Assign(to, value) => ()
      case If(cond, body) => ()
      case Seq(s1, _) =>
        noRedeclStmtNoRedeclaredVar(s1, state)
  }.ensuring(
    Interpreter.traceStmt1(Cmd(stmt, state)) match
      case Right(_)         => true
      case Left(exceptions) => !exceptions.contains(LangException.RedeclaredVariable)
  )


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

  */
  /*
  def test(stmt: Stmt, state: State): Unit = {
    require(Interpreter.evalStmt(stmt, state).isRight)
    val newState = Interpreter.evalStmt(stmt, state)
  }.ensuring(Interpreter)
  */

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
