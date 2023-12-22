package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import stainless.annotation.{extern, pure}
import stainless.proof.check

import Expr.*
import Stmt.*
import Conf.*


object Proofs {

  // ---
  // Interpreter

  private def envStackInclusion(env: Env, envs: List[Env]): Boolean = envs match
    case Cons(h, t) => keySet(h).subsetOf(keySet(env)) && envStackInclusion(h, t) 
    case Nil() => true

  private def blocksAreToplevel(stmt: Stmt): (Boolean, BigInt) = {
    stmt match
      case Decl(name, value) => (true, BigInt(0))
      case Assign(to, value) => (true, BigInt(0))
      case If(cond, body) =>
        val (b, i) = blocksAreToplevel(body)
        (b && i == 0, i)
      case Seq(stmt1, stmt2) =>
        val (b1, i1) = blocksAreToplevel(stmt1)
        val (b2, i2) = blocksAreToplevel(stmt2)
        (b1 && b2 && i2 == 0, i1)
      case _Block(stmt0) =>
        val (b, i) = blocksAreToplevel(stmt0)
        (b, i + 1)
  }.ensuring(res => res._2 >= 0)
  
  def stmtAndStateAreConsistent(stmt: Stmt, state: State, blocks: BigInt): Boolean =
    val (b, i) = blocksAreToplevel(stmt)
    blocks >= 0 && b && i + blocks + 1 == state._1.size && envStackInclusion(state._1.head, state._1.tail)

  def stateIsConsistent(state: State, blocks: BigInt): Boolean =
    blocks >= 0 && blocks + 1 == state._1.size && envStackInclusion(state._1.head, state._1.tail)


  @extern // TODO: prove
  def stmtHasNoBlocksIsConsistent(stmt: Stmt, state: State): Unit = {
    require(state._1.nonEmpty)
    require(Checker.stmtHasNoBlocks(stmt))
  }.ensuring(
    stmtAndStateAreConsistent(stmt, state, 0)
  )

  def evalStmt1Consistency(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, blocks))
    stmt match
      case Decl(name, value) =>
        subsetTest(state._1.head, name, state._3)
      case Seq(stmt1, stmt2) =>
        evalStmt1Consistency(stmt, state, blocks)
      case _Block(stmt0) =>
        evalStmt1Consistency(stmt0, state, blocks + 1)
      case _ => ()
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(nstate) => stateIsConsistent(nstate, blocks)
        case Cmd(nstmt, nstate) => stmtAndStateAreConsistent(nstmt, nstate, blocks)
  )

  // ---

  def closedExprEval(expr: Expr, state: State): Unit = {
    require(state._1.nonEmpty)
    val keys = keySet(state._1.head)
    require(Checker.exprIsClosed(expr, keys))
    expr match
      case True => ()
      case False => ()
      case Nand(left, right) =>
        assert(Checker.exprIsClosed(left, keys))
        assert(Checker.exprIsClosed(right, keys))
        closedExprEval(left, state)
        closedExprEval(right, state)
      case Ident(name) =>
        keySetPost(state._1.head, name)
        assert(state._1.head.contains(name))
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_) => true
      case Left(exceptions) =>
        !exceptions.contains(LangException.UndeclaredVariable)
        && !exceptions.contains(LangException._EmptyEnvStack)
  )

  def evalStmt1Aux(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, blocks))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    evalStmt1Consistency(stmt, state, blocks)
    closedStmtEvalPlusClosedness1(stmt, state, blocks)
    stmt match
      case Decl(name, value) =>
        consistentKeySet(keys, state._1.head, name, state._3)
      case Assign(to, value) => ()
      case If(cond, body) => ()
      case Seq(stmt1, stmt2) =>
        Interpreter.evalStmt1(stmt1, state, blocks) match
          case Left(b) => () 
          case Right(conf) => conf match
            case St(nstate) => ()
            case Cmd(nstmt1, nstate) =>
              evalStmt1Aux(Seq(nstmt1, stmt2), nstate, blocks)
      case _Block(stmt0) =>
        Interpreter.evalStmt1(stmt0, state, blocks + 1) match
          case Left(b) => () 
          case Right(conf) => conf match
            case St(nstate) => ()
            case Cmd(nstmt0, nstate) =>
              evalStmt1Aux(_Block(nstmt0), nstate, blocks)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_) => true 
      case Right(conf) => conf match
        case St(nstate) =>
          stateIsConsistent(nstate, blocks) &&
          (Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == keySet(nstate._1.head))
        case Cmd(nstmt, nstate) =>
          stmtAndStateAreConsistent(nstmt, nstate, blocks) &&
          (Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._2)
  )

  def closedStmtEvalPlusClosedness1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, blocks))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    evalStmt1Consistency(stmt, state, blocks)
    evalStmt1Aux(stmt, state, blocks)
    stmt match
      case Decl(name, value) =>
        closedExprEval(value, state)
      case Assign(to, value) =>
        closedExprEval(value, state)
        keySetPost(state._1.head, to)
      case If(cond, body)    =>
        closedExprEval(cond, state)
      case Seq(stmt1, stmt2) =>
        closedStmtEvalPlusClosedness1(stmt1, state, blocks)
      case _Block(stmt0)       =>
        closedStmtEvalPlusClosedness1(stmt0, state, blocks + 1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Right(conf) => conf match
        case St(nstate) =>
          stateIsConsistent(nstate, blocks)
        case Cmd(nstmt, nstate) =>
          stmtAndStateAreConsistent(nstmt, nstate, blocks)
          && Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._1
      case Left(exceptions) =>
        !exceptions.contains(LangException.UndeclaredVariable)
        && !exceptions.contains(LangException._EmptyEnvStack)
  )

  def closedStmtEval(stmt: Stmt, state: State): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, 0))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    evalStmt1Consistency(stmt, state, 0)
    closedStmtEvalPlusClosedness1(stmt, state, 0)
    Interpreter.evalStmt1(stmt, state, 0) match
      case Left(_) => ()
      case Right(conf) => conf match
        case St(nstate) => ()
        case Cmd(nstmt, nstate) =>
          closedStmtEval(nstmt, nstate)
  }.ensuring(
    Interpreter.evalStmt(stmt, state) match
      case Right(fstate) => true
      case Left(exceptions) =>
        !exceptions.contains(LangException.UndeclaredVariable)
        && !exceptions.contains(LangException._EmptyEnvStack)
  )

  // Rest

  /*
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
