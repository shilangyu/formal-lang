package lang

import stainless.*
import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
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

  def closedStmtNoUndeclaredVar(stmt: Stmt, state: State): Unit = {
    val env = state._1
    require(Checker.isStmtClosed(stmt, env)._1)
    stmt match
      case Decl(name, value)  =>
        closedExprEvaluates(value, state)
      case Assign(to, value)  =>
        closedExprEvaluates(value, state)
        assert(env.head.contains(to))
      case If(cond, body)     =>
        assert(Checker.isExprClosed(cond, env.head))
        closedExprEvaluates(cond, state)
      case While(cond, body)     =>
        assert(Checker.isExprClosed(cond, env.head))
        closedExprEvaluates(cond, state)
      case Seq(stmt1, _)      =>
        closedStmtNoUndeclaredVar(stmt1, state)
      case Block(true, stmt1)   =>
        assert(env.head == env.push(env.head).head)
        assert(Checker.isStmtClosed(stmt1, env.push(env.head))._1)
        closedStmtNoUndeclaredVar(stmt1, (env.push(env.head), state._2, state._3))
      case Block(false, stmt1)  =>
        closedStmtNoUndeclaredVar(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  def closenessIsPreserved(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val env = state._1
    require(Checker.isStmtClosed(stmt, env)._1)
    stmt match
      case Decl(name, value) =>
        closedExprEvaluates(value, state)
      case Assign(to, value)  =>
        closedExprEvaluates(value, state)
        assert(env.head.contains(to))
      case If(cond, body)     =>
        assert(Checker.isExprClosed(cond, env.head))
        closedExprEvaluates(cond, state)
      case While(cond, body)     =>
        assert(Checker.isExprClosed(cond, env.head))
        closedExprEvaluates(cond, state)
      case Seq(stmt1, stmt2)      => stmt1 match
        case Decl(_, _) => ()
        case Assign(_, _) => ()
        case If(_, _) => ()
        case While(_, _) => ()
        case Seq(_, _) =>
          closenessIsPreserved(stmt1, state)
          Interpreter.traceStmt1(stmt1, state) match
            case Right(conf) => conf match
              case St(state1) => ()
              case Cmd(nstmt1, state1) => 
                assert(Checker.isStmtClosed(nstmt1, state1._1)._1)
                closenessIsPreserved(Seq(nstmt1,stmt2), state1)
            case Left(_) => ()
        case Block(true, _) =>
          closenessIsPreserved(stmt1, (env.push(env.head), state._2, state._3))
          Interpreter.traceStmt1(stmt1, state) match
            case Right(conf) => conf match
              case St(state1) => ()
              case Cmd(nstmt1, state1) => 
                assert(Checker.isStmtClosed(nstmt1, state1._1)._1)
            case Left(_) => ()
        case Block(false, _) =>
          closenessIsPreserved(stmt1, state)
          Interpreter.traceStmt1(stmt1, state) match
            case Right(conf) => conf match
              case St(state1) => ()
              case Cmd(nstmt1, state1) => 
                assert(Checker.isStmtClosed(nstmt1, state1._1)._1)
            case Left(_) => ()
        closedStmtNoUndeclaredVar(stmt1, state)
        Interpreter.traceStmt1(stmt, state) match
          case Right(conf) => conf match
            case St(state1) => ()
            case Cmd(nstmt1, state1) => 
              assert(Checker.isStmtClosed(nstmt1, state1._1)._1)
          case Left(_) => ()
      case Block(true, stmt1)   =>
        assert(env.head == env.push(env.head).head)
        assert(Checker.isStmtClosed(stmt1, env.push(env.head))._1)
        closedStmtNoUndeclaredVar(stmt1, (env.push(env.head), state._2, state._3))
        closenessIsPreserved(stmt1, (env.push(env.head), state._2, state._3))
      case Block(false, stmt1)  =>
        closedStmtNoUndeclaredVar(stmt1, state)
        closenessIsPreserved(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Right(conf) => conf match
        case St(state1) => true
        case Cmd(stmt1, state1) => Checker.isStmtClosed(stmt1, state1._1)._1
      case Left(_) => true
    )
  */

  /*
  def noRedeclStmtNoRedeclaredVar(stmt: Stmt, state: State): Unit = {
    val env = state._1
    require(Checker.noRedecl(stmt, env)._1)
    stmt match
      case Decl(name, value) =>
        assert(!env.head.contains(name))
      case Assign(to, value) => ()
      case If(cond, body) =>
        assert(body.isInstanceOf[Block])
      case Seq(stmt1, _) =>
        noRedeclStmtNoRedeclaredVar(stmt1, state)
      case Block(true, stmt1)   =>
        assert(Checker.noRedecl(stmt1, env.push(env.head))._1)
        noRedeclStmtNoRedeclaredVar(stmt1, (env.push(env.head), state._2, state._3))
      case Block(false, stmt1)  =>
        assert(Checker.noRedecl(stmt1, env)._1)
        noRedeclStmtNoRedeclaredVar(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Right(_)         => true
      case Left(exceptions) => !exceptions.contains(LangException.RedeclaredVariable)
  )
  */

  def locIncreases(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val env = state._1
    stmt match
      case Decl(_, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(state1) =>
              assert(state1._3 == state._3 + 1)
            case _ => ()
      case While(cond, body) => ()
      case Seq(stmt1, _)   => 
        locIncreases(stmt1, state)
      case Block(true, stmt1)   => 
        locIncreases(stmt1, (env.push(env.head), state._2, state._3))
      case Block(false, stmt1)   => 
        locIncreases(stmt1, state)
      case _            => ()
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(state1) => state1._3 >= state._3
/*
          if stmt.isInstanceOf[Decl] then newState._3 == state._3 + 1
          else newState._3 == state._3
          */
        case Cmd(_, state1) => state1._3 >= state._3
    )

  /*
  def test(stmt: Stmt, state: State): Unit = {
    require(Interpreter.evalStmt(stmt, state).isRight)
    val newState = Interpreter.evalStmt(stmt, state)
  }.ensuring(Interpreter)
  */

  @extern @pure
  def mapsUpdate(map: Mem, x: Loc, y: Boolean): Unit = {
    require(map.contains(x))
  }.ensuring(_ => map.updated(x, y).keys == map.keys)

  def locIncreasesByOne(stmt: Stmt, state: State): Unit = {
    //require(Interpreter.traceStmt1(stmt, state).isRight) 
    decreases(stmt)
    val env = state._1
    val mem = state._2
    val nl = state._3
    require(!mem.contains(nl))
    locIncreases(stmt, state)

    stmt match
      case Decl(_, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._3 == state._3 + 1)
              assert(!(nstate._2.keys.length > state._2.keys.length) || nstate._3 == state._3 + 1)
            case _ => ()
      case Assign(to, value) => env.head.get(to) match 
        case Some(loc) => mem.get(loc) match
          case Some(_) => 
            Interpreter.traceStmt1(stmt, state) match
              case Left(_)      => ()
              case Right(conf)  => conf match
                case St(nstate) =>
                  assert(nstate._3 == state._3)
                  mapsUpdate(mem, loc, value)
                  assert(!(mem.contains(loc)) || nstate._2.keys == state._2.keys)
                case Cmd(_, nstate) => 
                  assert(nstate._2.keys.length == state._2.keys.length)
          case None() => ()
        case None() => ()
      case Seq(stmt1, _)   => 
        locIncreasesByOne(stmt1, state)
      case Block(true, stmt1)   => 
        locIncreasesByOne(stmt1, (env.push(env.head), state._2, state._3))
      case Block(false, stmt1)   => 
        locIncreasesByOne(stmt1, state)
      case _ => ()
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(nstate) => 
          !(nstate._2.keys.length > state._2.keys.length) || nstate._3 == state._3 + 1
        case Cmd(_, nstate) => 
          !(nstate._2.keys.length > state._2.keys.length) || nstate._3 == state._3 + 1
    )

}
