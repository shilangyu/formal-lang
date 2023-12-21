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

  @extern 
  def noBlocksStmtToToplevelblocks(stmt: Stmt, state: State): Unit = {
    require(state._1.nonEmpty)
    require(Checker.stmtHasNoBlocks(stmt))
  }.ensuring( _ =>
    Interpreter.consistency(stmt, state, 0)
  )

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
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  @extern @pure
  def axiom2(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(Interpreter.consistency(stmt, state, blocks))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_) => true 
      case Right(conf) => conf match
        case St(nstate) =>
          (Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == keySet(nstate._1.head))
        case Cmd(nstmt, nstate) =>
          (Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._2)
  )
  */

  def evalStmt1Closeness(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(Interpreter.consistency(stmt, state, blocks))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    closedStmtEval1(stmt, state, blocks)
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
              evalStmt1Closeness(Seq(nstmt1, stmt2), nstate, blocks)
      case _Block(stmt0) =>
        Interpreter.evalStmt1(stmt0, state, blocks + 1) match
          case Left(b) => () 
          case Right(conf) => conf match
            case St(nstate) => ()
            case Cmd(nstmt0, nstate) =>
              evalStmt1Closeness(_Block(nstmt0), nstate, blocks)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_) => true 
      case Right(conf) => conf match
        case St(nstate) =>
          Interpreter.consistency(nstate, blocks) &&
          (Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == keySet(nstate._1.head))
        case Cmd(nstmt, nstate) =>
          Interpreter.consistency(nstmt, nstate, blocks) &&
          (Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._2)
  )

  def closedStmtEval1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(Interpreter.consistency(stmt, state, blocks))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    //axiom2(stmt, state, blocks)  // REMOVE
    evalStmt1Closeness(stmt, state, blocks)
    stmt match
      case Decl(name, value) =>
        closedExprEval(value, state)
      case Assign(to, value) =>
        closedExprEval(value, state)
        keySetPost(state._1.head, to)
        //assert(state._1.head.contains(to))
      case If(cond, body)    =>
        closedExprEval(cond, state)
        //assert(Checker.stmtIsClosed(body, keys)._1)
      case Seq(stmt1, stmt2) =>
        //assert(Checker.stmtIsClosed(stmt1, keys)._1)
        closedStmtEval1(stmt1, state, blocks)
        Interpreter.evalStmt1(stmt1, state, blocks) match
          case Left(_)     => () 
          case Right(conf) => conf match
            case St(nstate)          => ()
              //assert(nstate._1.nonEmpty)
              //assert(nstate._1 != Nil())
              //assert(Checker.stmtIsClosed(stmt2, keySet(nstate._1.head))._1)
            case Cmd(nstmt1, nstate) => ()
              //assert(nstate._1.nonEmpty)
              //assert(nstate._1 != Nil())
              //assert(
              //  Checker.stmtIsClosed(stmt1, keys)._2
              //    == Checker.stmtIsClosed(nstmt1, keySet(nstate._1.head))._2
              //)
              //assert(Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate._1.head))._1)
      case _Block(stmt0)       =>
        //assert(Checker.stmtIsClosed(stmt, keys)._1)
        closedStmtEval1(stmt0, state, blocks + 1)
        Interpreter.evalStmt1(stmt0, state, blocks + 1) match
          case Left(_)     => ()
          case Right(conf) => conf match
            case St(nstate)         => ()
              //assert(nstate._1.nonEmpty)
              //assert(nstate._1 != Nil())
            case Cmd(nstmt0, nstate) => ()
              //assert(nstate._1.nonEmpty)
              //assert(nstate._1 != Nil())
              //assert(Checker.stmtIsClosed(_Block(nstmt), keySet(nstate._1.head))._1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Right(conf) => conf match
        case St(nstate) =>
          Interpreter.consistency(nstate, blocks)
        case Cmd(nstmt, nstate) =>
          Interpreter.consistency(nstmt, nstate, blocks)
          && Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._1
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

  /*
  @extern
  def sub(stmt: Stmt, env1: Set[Name], env2: Set[Name]): Unit = {
    require(env1.subsetOf(env2))
    require(Checker.stmtIsClosed(stmt, env1)._1)
  }.ensuring(
    Checker.stmtIsClosed(stmt, env2)._1
  )

  @extern
  def stupid(stmt: Stmt, state: State): Unit = {
    require(state._1.nonEmpty)
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    /*
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
    */
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, false) match
      case Left(_) => true
      case Right(c) => c match
        case St(nstate) => true
          //Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
          //  == keySet(nstate._1.head)
        case Cmd(nstmt, nstate) =>
          val keys = keySet(nstate._1.head)
          Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            .subsetOf(Checker.stmtIsClosed(nstmt, keys)._2)
          //Checker.stmtIsClosed(nstmt, keySet(nstate._1))._2
  )

  def closedStmtEval1(stmt: Stmt, state: State, leaf: Boolean): Unit = {
    require(state._1.nonEmpty)
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    stmt match
      case Decl(name, value) =>
        closedExprEval(value, state)
        consistentKeySet(keys, state._1.head, name, state._3)
      case Assign(to, value) =>
        closedExprEval(value, state)
        keySetPost(state._1.head, to)
        assert(state._1.head.contains(to))
      case If(cond, body)    =>
        closedExprEval(cond, state)
        assert(Checker.stmtIsClosed(body, keys)._1)

      case Seq(stmt1, stmt2) =>

        assert(Checker.stmtIsClosed(stmt1, keys)._1)
        assert(Checker.stmtIsClosed(stmt2, Checker.stmtIsClosed(stmt1, keys)._2)._1)

        closedStmtEval1(stmt1, state, false)
        Interpreter.evalStmt1(stmt1, state, false) match
          case Left(_) => () 
          case Right(c) => c match
            case St(nstate) =>
              assert(Checker.stmtIsClosed(stmt2, keySet(nstate._1.head))._1)
            case Cmd(nstmt1, nstate) =>
              val nkeys = keySet(nstate._1.head)
              assert(Checker.stmtIsClosed(nstmt1, nkeys)._1)
              assert(keySet(state._1.head).subsetOf(nkeys))

              //stupid(stmt1, state)
              //assert(
              //  Checker.stmtIsClosed(stmt1, keySet(state._1.head))._2
              //    .subsetOf(Checker.stmtIsClosed(nstmt1, keys)._2)
              //)
              check(Checker.stmtIsClosed(Seq(nstmt1, stmt2), nkeys)._1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, leaf) match
      case Right(nconf) => nconf match
        case St(nstate) =>
          if leaf then true
          else
            nstate._1.nonEmpty
            && Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
              == keySet(nstate._1.head)
            && keySet(state._1.head).subsetOf(keySet(nstate._1.head))
        case Cmd(nstmt, nstate) =>
          nstate._1.nonEmpty
          && Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._1
          && keySet(state._1.head).subsetOf(keySet(nstate._1.head))
          //&& Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
          //    .subsetOf(Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._2)
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
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

  /*
  @extern
  def stupid(stmt: Stmt, state: State): Unit = {
    require(state._1.nonEmpty)
    /*
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
    */
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, true) match
      case Left(_) => true
      case Right(c) => c match
        case St(nstate) =>
          Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == keySet(nstate._1.head)
        case Cmd(nstmt, nstate) =>
          Checker.stmtIsClosed(stmt, keySet(state._1.head))._2
            == Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._2
          //Checker.stmtIsClosed(nstmt, keySet(nstate._1))._2
  )
  */
  
  /*
  def closedStmtEval1(stmt: Stmt, state: State): Unit = {
    require(state._1.nonEmpty)
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    stmt match
      case Decl(name, value) =>
        closedExprEval(value, state)
        consistentKeySet(keys, state._1.head, name, state._3)
      case Assign(to, value) =>
        closedExprEval(value, state)
        keySetPost(state._1.head, to)
        assert(state._1.head.contains(to))
      case If(cond, body)    =>
        closedExprEval(cond, state)
        assert(Checker.stmtIsClosed(body, keys)._1)        
      case Seq(stmt1, stmt2) =>
        assert(Checker.stmtIsClosed(stmt1, keys)._1)
        closedStmtEval1(stmt1, state)
        Interpreter.evalStmt1(stmt1, state, false) match
          case Left(_) => () 
          case Right(c) => c match
            case St(nstate) =>
              assert(Checker.stmtIsClosed(stmt2, keySet(nstate._1.head))._1)
            case Cmd(nstmt1, nstate) =>
              assert(Checker.stmtIsClosed(nstmt1, keySet(nstate._1.head))._1)
              stupid(stmt1, state)
              assert(
                Checker.stmtIsClosed(stmt1, keySet(state._1.head))._2
                  == Checker.stmtIsClosed(nstmt1, keySet(nstate._1.head))._2
              )
              assert(Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate._1.head))._1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, true) match
      case Right(nconf) => nconf match
        case St(nstate) =>
          Checker.stmtIsClosed(stmt, keySet(state._1.head))._2 == keySet(nstate._1.head)
        case Cmd(nstmt, nstate) =>
          Checker.stmtIsClosed(nstmt, keySet(nstate._1.head))._1
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )
  */

  def closedStmtEval(stmt: Stmt, state: State): Unit = {
    require(Interpreter.consistency(stmt, state, 0))
    val keys = keySet(state._1.head)
    require(Checker.stmtIsClosed(stmt, keys)._1)
    closedStmtEval1(stmt, state, 0)
    Interpreter.evalStmt1(stmt, state, 0) match
      case Left(_) => ()
      case Right(conf) => conf match
        case St(nstate) => ()
        case Cmd(nstmt, nstate) =>
          closedStmtEval(nstmt, nstate)
  }.ensuring(
    Interpreter.evalStmt(stmt, state) match
      case Right(fstate) => true
      case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
  )

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
