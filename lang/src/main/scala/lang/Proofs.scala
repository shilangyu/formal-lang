package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import stainless.proof.check
import stainless.annotation.extern
import stainless.annotation.pure

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


  /*
  def diffToHead(env: List[(Name, Loc)], name: Name, x: BigInt): Unit = {
  }.ensuring(
    ((name, 0) :: env).map(_._1) == ((name, x) :: env).map(_._1)
  )
  */

  @extern @pure
  def sameKeysProp(env: Env, state: State, name: Name, x: Loc): Unit = {
    require(env.keys.toSet == state._1.keys.toSet)
  }.ensuring(
    (env + (name -> 0)).keys.toSet == (state._1 + (name -> x)).keys.toSet
  )

  def checkerInterpreterSameKeys(stmt: Stmt, env: Env, state: State): Unit = {
    require(env.keys.toSet == state._1.keys.toSet)
    require(Checker.isStmtClosed(stmt, env)._1)
    require(Interpreter.evalStmt(stmt, state).isRight)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isStmtClosed(stmt, env)._2 == env + (name -> 0))
        assert(Interpreter.evalStmt(stmt, state).get._1 == state._1 + (name -> state._3))
        sameKeysProp(env, state, name, state._3)
      case Assign(to, value) => ()
      case If(cond, body) => ()
      case Seq(s1, s2) =>
        checkerInterpreterSameKeys(s1, env, state)
        assert(
          Checker.isStmtClosed(s1, env)._2.keys.toSet
            == Interpreter.evalStmt(s1, state).get._1.keys.toSet
        )
        val menv = Checker.isStmtClosed(s1, env)._2
        val mstate = Interpreter.evalStmt(s1, state).get
        checkerInterpreterSameKeys(s2, menv, mstate)
  }.ensuring( _ =>
    Checker.isStmtClosed(stmt, env)._2.keys.toSet
      == Interpreter.evalStmt(stmt, state).get._1.keys.toSet
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
        assert(Checker.isStmtClosed(body, state._1)._1)
        closedStmtEvaluates(body, state)
      //case While(cond, body) => ()state, ??
      case Seq(s1, s2) =>
        assert(Checker.isStmtClosed(s1, state._1)._1)
        closedStmtEvaluates(s1, state)

        //val menv = Checker.isStmtClosed(s1, state._1)._2
        //val mstate = (menv, state._2, state._3)
        // Missing: connect mstate with actual mstate
        //assert(Checker.isStmtClosed(s2, mstate._1)._1)
        //closedStmtEvaluates(s2, mstate)

        Interpreter.evalStmt(s1, state) match
          case Left(_) => ()
          case Right(mstate) =>
            assert(state._1.keys.toSet == state._1.keys.toSet)
            assert(Checker.isStmtClosed(s1, state._1)._1)
            assert(Interpreter.evalStmt(s1, state).isRight)
            //checkerInterpreterSameKeys(s1, state._1, state)
            closedStmtEvaluates(s2, mstate)
  }.ensuring( _ =>
    //Checker.isStmtClosed(stmt, env)._2.keys.toSet
    //  == Interpreter.evalStmt(stmt, state).get._1.keys.toSet
    (
      Interpreter.evalStmt(stmt, state) match
        case Right(_) => true
        case Left(excep) => !excep.contains(LangException.UndeclaredVariable)
    )
  )
}