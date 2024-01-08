package lang

import stainless.*
import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
import stainless.collection.*

import stainless.lang.Map.MapOps

import Expr.*
import Stmt.*


object Proofs {

  @extern @pure
  def keySet(env: Env): Set[Name] = {
    Set.fromScala(env.theMap.keys.toSet)
  }

  @extern @pure
  def emptyKeySetPost(): Unit = {
  }.ensuring( _ =>
    Set.empty[Name] == keySet(Map.empty[Name, Loc])
  )

  @extern @pure
  def keySetPost(env: Env, name: Name): Unit = {
  }.ensuring( _ =>
    env.contains(name) == keySet(env).contains(name)
  )

  @extern @pure
  def consistencySetkeySet(names: Set[Name], env: Env, key: Name, loc: Loc): Unit = {
    require(names == keySet(env))
  }.ensuring( _ =>
    names + key == keySet(env + (key -> loc))
  )

  def closedExprEvaluates(expr: Expr, state: State): Unit = {
    val keys = keySet(state.env)
    require(Checker.isExprClosed(expr, keys))
    expr match
      case True => ()
      case False => ()
      case Nand(left, right) =>
        assert(Checker.isExprClosed(left, keys))
        assert(Checker.isExprClosed(right, keys))
        closedExprEvaluates(left, state)
        closedExprEvaluates(right, state)
        ()
      case Ident(name) =>
        keySetPost(state.env, name)
        assert(keys.contains(name))
        ()
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  def consistencyKeysCheckerInterpreter(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val keys = keySet(state.env)
    require(Checker.isStmtClosed(stmt, keys)._1)
    require(Interpreter.evalStmt(stmt, state).isRight)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isStmtClosed(stmt, keys)._2 == keys + name)
        assert(Interpreter.evalStmt(stmt, state).get.env == state.env + (name -> state.nextLoc))
        consistencySetkeySet(keys, state.env, name, state.nextLoc)
      case Assign(to, value) => ()
      case If(cond, body) => ()
      case Seq(stmt1, stmt2) =>
        assert(Checker.isStmtClosed(stmt1, keys)._1)
        assert(Interpreter.evalStmt(stmt1, state).isRight)
        consistencyKeysCheckerInterpreter(stmt1, state)
        assert(
          Checker.isStmtClosed(stmt1, keys)._2
            == keySet(Interpreter.evalStmt(stmt1, state).get.env)
        )
        val mnames = Checker.isStmtClosed(stmt1, keys)._2
        assert(Checker.isStmtClosed(stmt2, mnames)._1)
        Interpreter.evalStmt(stmt1, state) match
          case Left(_) => () 
          case Right(mstate) =>
            assert(mnames == keySet(mstate.env))
            assert(Checker.isStmtClosed(stmt2, keySet(mstate.env))._1)
            assert(Interpreter.evalStmt(stmt2, mstate).isRight)
            consistencyKeysCheckerInterpreter(stmt2, mstate)
      case Free(name)        => ()
  }.ensuring( _ =>
    Checker.isStmtClosed(stmt, keySet(state.env))._2
      == keySet(Interpreter.evalStmt(stmt, state).get.env)
  )

  def closedStmtEvaluates(stmt: Stmt, state: State): Unit = {
    val keys = keySet(state.env)
    require(Checker.isStmtClosed(stmt, keys)._1)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isExprClosed(value, keys))
        closedExprEvaluates(value, state)
      case Assign(to, value) =>
        keySetPost(state.env, to)
        assert(state.env.contains(to))
        assert(Checker.isExprClosed(value, keys))
        closedExprEvaluates(value, state)
      case If(cond, body) =>
        assert(Checker.isExprClosed(cond, keys))
        closedExprEvaluates(cond, state)
        assert(Checker.isStmtClosed(body, keys)._1)
        closedStmtEvaluates(body, state)
      //case While(cond, body) => ()state, ??
      case Seq(stmt1, stmt2) =>
        assert(Checker.isStmtClosed(stmt1, keys)._1)
        closedStmtEvaluates(stmt1, state)

        Interpreter.evalStmt(stmt1, state) match
          case Left(_) => ()
          case Right(mstate) =>
            assert(Checker.isStmtClosed(stmt1, keys)._1)
            assert(Interpreter.evalStmt(stmt1, state).isRight)
            consistencyKeysCheckerInterpreter(stmt1, state)

            val mnames = Checker.isStmtClosed(stmt1, keys)._2
            assert(Checker.isStmtClosed(stmt2, mnames)._1)
            val mstate = Interpreter.evalStmt(stmt1, state).get
            assert(mnames == keySet(mstate.env))
            closedStmtEvaluates(stmt2, mstate)
      case Free(name)        =>
        assert(keys.contains(name))
        keySetPost(state.env, name)
        assert(state.env.contains(name))
  }.ensuring( _ =>
    Interpreter.evalStmt(stmt, state) match
      case Right(_) => true
      case Left(excep) => !excep.contains(LangException.UndeclaredVariable)
  )

  def closedProgramEvaluates(stmt: Stmt): Unit = {
    require(Checker.isProgClosed(stmt)._1)
    assert(Checker.isStmtClosed(stmt, Set.empty)._1)
    emptyKeySetPost()
    closedStmtEvaluates(stmt, State(Map.empty, Set.empty, Map.empty, 0))
  }.ensuring(
    Interpreter.evalStmt(stmt, State(Map.empty, Set.empty, Map.empty, 0)) match
      case Right(_) => true
      case Left(excep) => !excep.contains(LangException.UndeclaredVariable)
  )
}
