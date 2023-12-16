package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import stainless.annotation.extern

import Expr.*
import Stmt.*
import Conf.*


object Proofs {

  def closedExprEval(expr: Expr, state: State): Unit = {
    val keys = keySet(state._1)
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
        keySetPost(state._1, name)
        assert(state._1.contains(name))
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  def test(stmt: Stmt, conf: Conf): Unit = {
    Interpreter.evalStmt1(stmt, conf).isRight
    require(
      conf match
        case St(state) => true
        case Cmd(stmt, state) =>
          val keys = keySet(state._1)
          Checker.stmtIsClosed(stmt, keys)._1
    )
    conf match
      case St(state) => 
      case Cmd(stmt, state) =>
    
  }.ensuring(

  )
  */

  /*
  def test(seq: Stmt.Seq, state: State): Unit = {
    val keys = keySet(state._1)
    require(Checker.stmtIsClosed(seq, keys)._1)
    assert(Checker.stmtIsClosed(seq.stmt1, keys)._1)
    val menv = Checker.stmtIsClosed(seq.stmt1, keys)._2
    assert(Checker.stmtIsClosed(seq.stmt2, menv)._1)

    Interpreter.evalStmt1(seq, state) match
      case Left(b) => () 
      case Right(c) => c match
        case St(nstate) => ()
        case Cmd(nstmt, nstate) => ()
  }.ensuring(
    Interpreter.evalStmt1(seq, state) match
      case Left(b) => true
      case Right(c) => c match
        case St(nstate) =>
          Checker.stmtIsClosed(seq, keySet(state._1))._2 == keySet(nstate._1)
        case Cmd(stmt, state) => true
  )

  z = closed(x, y)
  p = closed(y, z)

  Close(Seq(a, b), e)
  (Seq(a', b), e') = onestep(Seq(a, b), e)
  Close(Seq(a', b), e')
  
  
  Closed(s, e) -> Closed(s, e+x)
  Closed(s, e) and next small step s == DEcl -> Closed(s', e+decl)
  */

  def stupid(stmt: Stmt, state: State): Unit = {
    val keys = keySet(state._1)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    //require(Interpreter.evalStmt1(stmt, state))
    stmt match
      case Decl(name, value) =>
        consistentKeySet(keys, state._1, name, state._3)
      case Assign(to, value) => ()
      case If(cond, body) =>
        assert(Checker.stmtIsClosed(body, keySet(state._1))._1)
        Interpreter.evalExpr(cond, state) match
          case Left(_) => ()
          case Right(c) =>
            if c then
              assert(
                Checker.stmtIsClosed(stmt, keySet(state._1))._2
                  == Checker.stmtIsClosed(body, keySet(state._1))._2
              )
      case Seq(stmt1, stmt2) =>
        assert(Checker.stmtIsClosed(stmt1, keySet(state._1))._1)
        stupid(stmt1, state)
        closedStmtEval1(stmt1, state)
        Interpreter.evalStmt1(stmt1, state) match
          case Left(_) => () 
          case Right(c) => c match
            case St(nstate) =>
              assert(
                Checker.stmtIsClosed(stmt, keySet(state._1))._2
                  == Checker.stmtIsClosed(stmt2, keySet(nstate._1))._2
              )
            case Cmd(nstmt1, nstate) =>
              assert(Checker.stmtIsClosed(nstmt1, keySet(nstate._1))._1)
              assert(
                Checker.stmtIsClosed(stmt1, keySet(state._1))._2
                  == Checker.stmtIsClosed(nstmt1, keySet(nstate._1))._2
              )
              assert(Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate._1))._1)
              val mid = Checker.stmtIsClosed(nstmt1, keySet(nstate._1))._2
              //stupid(Seq(nstmt1, stmt2), nstate)
              assert(Checker.stmtIsClosed(stmt2, mid)._1)
              assert(
                Checker.stmtIsClosed(stmt, keySet(state._1))._2
                  == Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate._1))._2
              )

  }.ensuring(
    Interpreter.evalStmt1(stmt, state) match
      case Left(_) => true
      case Right(c) => c match
        case St(nstate) =>
          Checker.stmtIsClosed(stmt, keySet(state._1))._2
            == keySet(nstate._1)
        case Cmd(nstmt, nstate) =>
          Checker.stmtIsClosed(stmt, keySet(state._1))._2
            == Checker.stmtIsClosed(nstmt, keySet(nstate._1))._2
          //Checker.stmtIsClosed(nstmt, keySet(nstate._1))._2
  )
  
  def closedStmtEval1(stmt: Stmt, state: State): Unit = {
    val keys = keySet(state._1)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    stmt match
      case Decl(name, value) =>
        closedExprEval(value, state)
        consistentKeySet(keys, state._1, name, state._3)
      case Assign(to, value) =>
        closedExprEval(value, state)
        keySetPost(state._1, to)
        assert(state._1.contains(to))
      case If(cond, body)    =>
        closedExprEval(cond, state)
        assert(Checker.stmtIsClosed(body, keys)._1)        
      case Seq(stmt1, stmt2) =>
        assert(Checker.stmtIsClosed(stmt1, keys)._1)
        closedStmtEval1(stmt1, state)
        Interpreter.evalStmt1(stmt1, state) match
          case Left(_) => () 
          case Right(c) => c match
            case St(nstate) =>
              assert(Checker.stmtIsClosed(stmt2, keySet(nstate._1))._1)
            case Cmd(nstmt1, nstate) =>
              assert(Checker.stmtIsClosed(nstmt1, keySet(nstate._1))._1)
              stupid(stmt1, state)
              assert(
                Checker.stmtIsClosed(stmt1, keySet(state._1))._2
                  == Checker.stmtIsClosed(nstmt1, keySet(nstate._1))._2
              )
              assert(Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate._1))._1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state) match
      case Right(nconf) => nconf match
        case St(nstate) =>
          Checker.stmtIsClosed(stmt, keySet(state._1))._2 == keySet(nstate._1)
        case Cmd(nstmt, nstate) =>
          Checker.stmtIsClosed(nstmt, keySet(nstate._1))._1
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  def closedStmtEval(stmt: Stmt, state: State): Unit = {
    val keys = keySet(state._1)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    closedStmtEval1(stmt, state)
    Interpreter.evalStmt1(stmt, state) match
      case Left(_) => ()
      case Right(conf) => conf match
        case St(nstate) =>
          assert(Checker.stmtIsClosed(stmt, keySet(state._1))._2 == keySet(nstate._1))
        case Cmd(nstmt, nstate) =>
          closedStmtEval(nstmt, nstate)
  }.ensuring(
    Interpreter.evalStmt(stmt, state) match
      case Right(fstate) =>
        Checker.stmtIsClosed(stmt, keySet(state._1))._2 == keySet(fstate._1)
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )
  */

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
