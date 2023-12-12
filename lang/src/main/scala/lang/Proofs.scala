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
  def keySetPost(env: Env, name: Name): Unit = {
    ()
  }.ensuring( _ =>
    env.contains(name) == keySet(env).contains(name)
  )

  @extern @pure
  def emptyKeySetPost(): Unit = {
    ()
  }.ensuring( _ =>
    Set.empty[Name] == keySet(Map.empty[Name, Loc])
  )

  @extern @pure
  def sameKeyAdd(names: Set[Name], env: Env, key: Name, loc: Loc): Unit = {
    require(names == keySet(env))
  }.ensuring( _ =>
    names + key == keySet(env + (key -> loc))
  )

  def closedExprEvaluates(expr: Expr, state: State): Unit = {
    val keys = keySet(state._1)
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
        keySetPost(state._1, name)
        assert(keys.contains(name))
        ()
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  def checkerInterpreterSameKeys(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val keys = keySet(state._1)
    require(Checker.isStmtClosed(stmt, keys)._1)
    require(Interpreter.evalStmt(stmt, state).isRight)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isStmtClosed(stmt, keys)._2 == keys + name)
        assert(Interpreter.evalStmt(stmt, state).get._1 == state._1 + (name -> state._3))
        sameKeyAdd(keys, state._1, name, state._3)
      case Assign(to, value) => ()
      case If(cond, body) => ()
      case Seq(s1, s2) =>
        assert(Checker.isStmtClosed(s1, keys)._1)
        assert(Interpreter.evalStmt(s1, state).isRight)
        checkerInterpreterSameKeys(s1, state)
        assert(
          Checker.isStmtClosed(s1, keys)._2
            == keySet(Interpreter.evalStmt(s1, state).get._1)
        )
        val mnames = Checker.isStmtClosed(s1, keys)._2
        assert(Checker.isStmtClosed(s2, mnames)._1)
        Interpreter.evalStmt(s1, state) match
          case Left(_) => () 
          case Right(mstate) =>
            assert(mnames == keySet(mstate._1))
            assert(Checker.isStmtClosed(s2, keySet(mstate._1))._1)
            assert(Interpreter.evalStmt(s2, mstate).isRight)
            checkerInterpreterSameKeys(s2, mstate)
  }.ensuring( _ =>
    Checker.isStmtClosed(stmt, keySet(state._1))._2
      == keySet(Interpreter.evalStmt(stmt, state).get._1)
  )

  def closedStmtEvaluates(stmt: Stmt, state: State): Unit = {
    val keys = keySet(state._1)
    require(Checker.isStmtClosed(stmt, keys)._1)
    stmt match
      case Decl(name, value) =>
        assert(Checker.isExprClosed(value, keys))
        closedExprEvaluates(value, state)
      case Assign(to, value) =>
        keySetPost(state._1, to)
        assert(state._1.contains(to))
        assert(Checker.isExprClosed(value, keys))
        closedExprEvaluates(value, state)
      case If(cond, body) =>
        assert(Checker.isExprClosed(cond, keys))
        closedExprEvaluates(cond, state)
        assert(Checker.isStmtClosed(body, keys)._1)
        closedStmtEvaluates(body, state)
      //case While(cond, body) => ()state, ??
      case Seq(s1, s2) =>
        assert(Checker.isStmtClosed(s1, keys)._1)
        closedStmtEvaluates(s1, state)

        Interpreter.evalStmt(s1, state) match
          case Left(_) => ()
          case Right(mstate) =>
            assert(Checker.isStmtClosed(s1, keys)._1)
            assert(Interpreter.evalStmt(s1, state).isRight)
            checkerInterpreterSameKeys(s1, state)

            val mnames = Checker.isStmtClosed(s1, keys)._2
            assert(Checker.isStmtClosed(s2, mnames)._1)
            val mstate = Interpreter.evalStmt(s1, state).get
            assert(mnames == keySet(mstate._1))

            closedStmtEvaluates(s2, mstate)
  }.ensuring( _ =>
    Interpreter.evalStmt(stmt, state) match
      case Right(_) => true
      case Left(excep) => !excep.contains(LangException.UndeclaredVariable)
  )

  def closedProgramEvaluates(stmt: Stmt): Unit = {
    require(Checker.isProgClosed(stmt)._1)
    assert(Checker.isStmtClosed(stmt, Set.empty)._1)
    emptyKeySetPost()
    closedStmtEvaluates(stmt, (Map.empty, Map.empty, 0))
  }.ensuring(
    Interpreter.evalStmt(stmt, (Map.empty, Map.empty, 0)) match
      case Right(_) => true
      case Left(excep) => !excep.contains(LangException.UndeclaredVariable)
  )
}