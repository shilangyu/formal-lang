package lang

import stainless.*
import stainless.annotation.extern
import stainless.annotation.pure
import stainless.collection.*
import stainless.lang.*
import stainless.proof.check

import Expr.*
import Stmt.*
import Conf.*

object Proofs {

  // ---
  // Interpreter

  private def envStackInclusion(env: Env, envs: List[Env]): Boolean = envs match
    case Cons(h, t) => keySet(h).subsetOf(keySet(env)) && envStackInclusion(h, t)
    case Nil()      => true

  private def blocksAreToplevel(stmt: Stmt): (Boolean, BigInt) = {
    stmt match
      case Decl(name, value) => (true, BigInt(0))
      case Assign(to, value) => (true, BigInt(0))
      case If(cond, body)    =>
        val (b, i) = blocksAreToplevel(body)
        (b && i == 0, i)
      case Seq(stmt1, stmt2) =>
        val (b1, i1) = blocksAreToplevel(stmt1)
        val (b2, i2) = blocksAreToplevel(stmt2)
        (b1 && b2 && i2 == 0, i1)
      case Free(name)        => (true, BigInt(0))
      case _Block(stmt0)     =>
        val (b, i) = blocksAreToplevel(stmt0)
        (b, i + 1)
  }.ensuring(res => res._2 >= 0)

  def stmtAndStateAreConsistent(stmt: Stmt, state: State, blocks: BigInt): Boolean =
    val (b, i) = blocksAreToplevel(stmt)
    blocks >= 0 && b && i + blocks + 1 == state.envs.size && envStackInclusion(
      state.envs.head,
      state.envs.tail
    )

  def stateIsConsistent(state: State, blocks: BigInt): Boolean =
    blocks >= 0 && blocks + 1 == state.envs.size && envStackInclusion(
      state.envs.head,
      state.envs.tail
    )

  @extern // TODO: prove
  def stmtHasNoBlocksIsConsistent(stmt: Stmt, state: State): Unit = {
    require(state.envs.nonEmpty)
    require(Checker.stmtHasNoBlocks(stmt))
  }.ensuring(
    stmtAndStateAreConsistent(stmt, state, 0)
  )

  def evalStmt1Consistency(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, blocks))
    stmt match
      case Decl(name, value) =>
        subsetTest(state.envs.head, name, state.nextLoc)
        // ---
        assert((state.envs.head + (name -> state.nextLoc) :: state.envs.tail).size == blocks + 1)
        
      case Seq(stmt1, stmt2) =>
        evalStmt1Consistency(stmt1, state, blocks)
        // ---
        Interpreter.evalStmt1(stmt1, state, blocks) match
          case Left(content) => ()
          case Right(conf) => conf match
            case St(nstate) =>
              assert(stateIsConsistent(nstate, blocks))
              assert(stmtAndStateAreConsistent(stmt2, nstate, blocks))
            case Cmd(nstmt1, nstate) =>
              assert(stmtAndStateAreConsistent(nstmt1, nstate, blocks))
              assert(stmtAndStateAreConsistent(Seq(nstmt1, stmt2), nstate, blocks))
      case _Block(stmt0)     =>
        evalStmt1Consistency(stmt0, state, blocks + 1)
        // ---
        Interpreter.evalStmt1(stmt0, state, blocks + 1) match
          case Left(content) => ()
          case Right(conf) => conf match
            case St(nstate) =>
              assert(stateIsConsistent(nstate, blocks + 1))
              assert(nstate.envs.size == blocks + 2)
              assert(nstate.envs.tail.size == blocks + 1)
              assert(envStackInclusion(nstate.envs.tail.head, nstate.envs.tail.tail))
            case Cmd(nstmt0, nstate) =>
              assert(stmtAndStateAreConsistent(nstmt0, nstate, blocks + 1))
              assert(stmtAndStateAreConsistent(_Block(nstmt0), nstate, blocks))
      case Assign(to, value) =>
        // ---
        assert(state.envs.size == blocks + 1)
      case If(cond, body) =>
        // ---
        assert(state.envs.size == blocks + 1)
      case Free(name) =>
        // ---
        assert(state.envs.size == blocks + 1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_)     => true
      case Right(conf) =>
        conf match
          case St(nstate)         => stateIsConsistent(nstate, blocks)
          case Cmd(nstmt, nstate) => stmtAndStateAreConsistent(nstmt, nstate, blocks)
  )

  // ---

  @extern
  def cAxiom[T](a: List[T], x: BigInt, b: List[T]): Unit = {
    require(a.drop(x).tail == b.tail)
  }.ensuring(
    a(x + 1) == b.tail(0)
    && a.drop(x + 1) == b.tail
  )

  @extern
  def dAxiom[T](a: List[T], x: BigInt, b: List[T], y: BigInt): Unit = {
    require(a.drop(x).tail == b.drop(y).tail)
  }.ensuring(
    a(x + 1) == b(y + 1)
    && a.drop(x + 1) == b.drop(y + 1)
  )

  /** Lemmas and proofs of closedness: A program is closed if whenever evaluating Ident〈name〉 or
    * Assign〈name, expr〉, env(name) is defined.
    */
  object Closedness {
    def closedExprEval(expr: Expr, state: State): Unit = {
      require(state.envs.nonEmpty)
      val keys = keySet(state.envs.head)
      require(Checker.exprIsClosed(expr, keys))
      expr match
        case True              => ()
        case False             => ()
        case Nand(left, right) =>
          assert(Checker.exprIsClosed(left, keys))
          assert(Checker.exprIsClosed(right, keys))
          closedExprEval(left, state)
          closedExprEval(right, state)
        case Ident(name)       =>
          keySetPost(state.envs.head, name)
          assert(state.envs.head.contains(name))
    }.ensuring(
      Interpreter.evalExpr(expr, state) match
        case Right(_)         => true
        case Left(exceptions) =>
          !exceptions.contains(LangException.UndeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    @extern @pure
    def evalStmt1Aux(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs(0))
      require(Checker.stmtIsClosed(stmt, keys)._1)

      evalStmt1Consistency(stmt, state, blocks)
      
      assert(state.envs != Nil())

      stmt match
        case Decl(name, value) =>
          consistentKeySet(keys, state.envs(0), name, state.nextLoc)
          
          assert(keys + name == keySet(state.envs(0) + (name -> state.nextLoc)))
          assert(blocksAreToplevel(stmt)._2 == 0)
          assert(Checker.stmtIsClosed(stmt, keys)._2 == keySet((state.envs.head + (name -> state.nextLoc) :: state.envs.tail)(0)))

          assert((state.envs.head + (name -> state.nextLoc) :: state.envs.tail).size == blocks + 1)

          assert(state.envs.drop(0).tail == (state.envs.head + (name -> state.nextLoc) :: state.envs.tail).tail)
        case Assign(to, value) =>

          assert(blocksAreToplevel(stmt)._2 == 0)
          assert(keys == keySet(state.envs(0)))
          assert(Checker.stmtIsClosed(stmt, keys)._2 == keys)

          assert(state.envs.size == blocks + 1)

          assert(state.envs.drop(0).tail == state.envs.tail)
        case If(cond, body)    =>

          assert(blocksAreToplevel(stmt)._2 == 0)
          Interpreter.evalExpr(cond, state) match
            case Left(_) => () 
            case Right(c) =>
              if c then
                assert(blocksAreToplevel(_Block(body))._2 == 1)
                assert(state.envs.size == blocks + 1)
                assert(keySet((state.envs.head :: state.envs)(1)) == keys)
                assert(Checker.stmtIsClosed(stmt, keys)._2 == Checker.stmtIsClosed(_Block(body), keySet((state.envs.head :: state.envs)(1)))._2)

                assert((state.envs.head :: state.envs).size == blocks + 2)

                assert(state.envs.drop(0).tail == (state.envs.head :: state.envs).drop(1).tail)

                assert(state.envs.drop(0) != Nil())
                assert((state.envs.head :: state.envs).drop(1) != Nil())
              else
                assert(Checker.stmtIsClosed(stmt, keys)._2 == keys)
                assert(state.envs.size == blocks + 1)
                assert(state.envs.drop(0).tail == state.envs.tail)
        case Seq(stmt1, stmt2) =>
          evalStmt1Consistency(stmt1, state, blocks)  // JIC
          closedStmtEvalPlusClosedness1(stmt1, state, blocks)  // JIC

          evalStmt1Aux(stmt1, state, blocks)
          assert(blocksAreToplevel(stmt)._2 == blocksAreToplevel(stmt1)._2)

          assert(state.envs.size == blocksAreToplevel(stmt)._2 + blocks + 1)
          assert(state.envs.size > blocksAreToplevel(stmt)._2)

          Interpreter.evalStmt1(stmt1, state, blocks) match
            case Left(b)     => ()
            case Right(conf) =>
              conf match
                case St(nstate)          =>
                  assert(blocksAreToplevel(stmt2)._2 == 0)

                  assert(stateIsConsistent(nstate, blocks))
                  assert(nstate.envs.size == blocks + 1)

                  val bl = blocksAreToplevel(stmt1)._2

                  assert(blocksAreToplevel(stmt)._2 == bl)

                  assert(Checker.stmtIsClosed(stmt1, keySet(state.envs(bl)))._2 == keySet(nstate.envs(0)))
                  assert(Checker.stmtIsClosed(stmt, keySet(state.envs(bl)))._2 == Checker.stmtIsClosed(stmt2, keySet(nstate.envs(0)))._2)

                  assert(state.envs.drop(bl) != Nil())
                  assert(nstate.envs.drop(0) != Nil())
                case Cmd(nstmt1, nstate) =>

                  val bl = blocksAreToplevel(stmt1)._2
                  val nbl = blocksAreToplevel(nstmt1)._2
                  assert(nstate.envs.size == nbl + blocks + 1)
                  assert(nstate.envs.size > nbl)
                  assert(nstate.envs.drop(nbl).size > 0)

                  evalStmt1Aux(stmt1, state, blocks)
                  assert(state.envs.drop(bl).tail == nstate.envs.drop(nbl).tail)
                  assert(Checker.stmtIsClosed(stmt1, keySet(state.envs(bl)))._2 == Checker.stmtIsClosed(nstmt1, keySet(nstate.envs(nbl)))._2)

                  assert(nbl == blocksAreToplevel(Seq(nstmt1, stmt2))._2)

                  //evalStmt1Aux(Seq(nstmt1, stmt2), nstate, blocks)

                  assert(Checker.stmtIsClosed(stmt, keySet(state.envs(bl)))._2 == Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate.envs(nbl)))._2)

                  assert(state.envs.drop(bl) != Nil())
                  assert(nstate.envs.drop(nbl) != Nil())
        case Free(name)        =>

          assert(blocksAreToplevel(stmt)._2 == 0)
          assert(keys == keySet(state.envs(0)))
          assert(Checker.stmtIsClosed(stmt, keys)._2 == keys)

          assert(state.envs.size == blocks + 1)

          assert(state.envs.drop(0).tail == state.envs.tail)
        case _Block(stmt0)     =>
          evalStmt1Consistency(stmt0, state, blocks + 1)  // JIC
          closedStmtEvalPlusClosedness1(stmt0, state, blocks + 1)  // JIC

          evalStmt1Aux(stmt0, state, blocks + 1)
          assert(blocksAreToplevel(stmt)._2 == blocksAreToplevel(stmt0)._2 + 1)
          assert(state.envs.size == blocksAreToplevel(stmt)._2 + blocks + 1)
          assert(state.envs.size > blocksAreToplevel(stmt)._2)

          Interpreter.evalStmt1(stmt0, state, blocks + 1) match
            case Left(b)     => ()
            case Right(conf) =>
              conf match
                case St(nstate)          =>

                  assert(nstate.envs.size == blocks + 2)
                  assert(nstate.envs.tail.size == blocks + 1)

                  val bl = blocksAreToplevel(stmt0)._2

                  assert(blocksAreToplevel(stmt)._2 == bl + 1)

                  assert(state.envs.drop(bl).tail == nstate.envs.tail)
                  assert(Checker.stmtIsClosed(stmt0, keySet(state.envs(bl)))._2 == keySet(nstate.envs(0)))

                  cAxiom(state.envs, bl, nstate.envs)
                  assert(state.envs(bl + 1) == nstate.envs.tail(0))
                  assert(Checker.stmtIsClosed(stmt, keySet(state.envs(bl + 1)))._2 == keySet(nstate.envs.tail(0)))

                  assert(state.envs.drop(bl + 1) != Nil())
                  assert(nstate.envs.tail != Nil())
                  assert(state.envs.drop(bl + 1).tail == nstate.envs.tail.tail)
                case Cmd(nstmt0, nstate) =>

                  val bl = blocksAreToplevel(stmt0)._2
                  val nbl = blocksAreToplevel(nstmt0)._2

                  assert(blocksAreToplevel(stmt)._2 == bl + 1)
                  assert(state.envs.size > bl)
                  assert(state.envs.drop(bl).size > 0)

                  assert(stmtAndStateAreConsistent(nstmt0, nstate, blocks + 1))
                  assert(nstate.envs.size == nbl + blocks + 2)
                  assert(nstate.envs.size > nbl)
                  assert(nstate.envs.drop(nbl).size > 0)

                  evalStmt1Aux(stmt0, state, blocks + 1)
                  assert(state.envs.drop(bl).tail == nstate.envs.drop(nbl).tail)
                  assert(Checker.stmtIsClosed(stmt0, keySet(state.envs(bl)))._2 == Checker.stmtIsClosed(nstmt0, keySet(nstate.envs(nbl)))._2)

                  assert(nbl + 1 == blocksAreToplevel(_Block(nstmt0))._2)

                  //evalStmt1Aux(_Block(nstmt0), nstate, blocks)

                  dAxiom(state.envs, bl, nstate.envs, nbl)
                  assert(state.envs(bl + 1) == nstate.envs(nbl + 1))

                  assert(Checker.stmtIsClosed(stmt, keySet(state.envs(bl + 1)))._2 == Checker.stmtIsClosed(_Block(nstmt0), keySet(nstate.envs(nbl + 1)))._2)

                  assert(state.envs.drop(bl + 1) != Nil())
                  assert(nstate.envs.drop(nbl + 1) != Nil())
                  assert(state.envs.drop(bl + 1).tail == nstate.envs.drop(nbl + 1).tail)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Left(_)     => true
        case Right(conf) =>
          conf match
            case St(nstate)         =>
              state.envs.drop(blocksAreToplevel(stmt)._2).tail == nstate.envs.tail && (Checker.stmtIsClosed(stmt, keySet(state.envs(blocksAreToplevel(stmt)._2)))._2 == keySet(nstate.envs(0)))
            case Cmd(nstmt, nstate) =>
              state.envs.drop(blocksAreToplevel(stmt)._2).tail == nstate.envs.drop(blocksAreToplevel(nstmt)._2).tail && (Checker.stmtIsClosed(stmt, keySet(state.envs(blocksAreToplevel(stmt)._2)))._2 == Checker.stmtIsClosed(nstmt, keySet(nstate.envs(blocksAreToplevel(nstmt)._2)))._2)
    )

    /*
    @extern @pure
    def evalStmt1Aux(seq: Seq, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(seq, state, blocks))
      assert(state.envs != Nil())
      Interpreter.evalStmt1(seq.stmt1, state, blocks) match
        case Left(_) => ()
        case Right(conf) => conf match
          case St(nstate) => () 
          case Cmd(nstmt1, nstate) =>
            assert(stmtAndStateAreConsistent(nstmt1, nstate, blocks))
            assert(stmtAndStateAreConsistent(Seq(nstmt1, seq.stmt2), nstate, blocks))
            assert(nstate.envs != Nil())
    }.ensuring(
      Interpreter.evalStmt1(seq, state, blocks) match
        case Left(_)     => true
        case Right(conf) =>
          conf match
            case St(nstate)         => true
            case Cmd(nstmt, nstate) =>
              (Checker.stmtIsClosed(seq, keySet(state.envs.head))._2
                == Checker.stmtIsClosed(nstmt, keySet(nstate.envs.head))._2)
    )
    */

    def closedStmtEvalPlusClosedness1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs(blocksAreToplevel(stmt)._2))
      require(Checker.stmtIsClosed(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)

      assert(state.envs != Nil())

      stmt match
        case Decl(name, value) =>
          closedExprEval(value, state)
        case Assign(to, value) =>
          closedExprEval(value, state)
          keySetPost(state.envs(0), to)
        case If(cond, body)    =>
          closedExprEval(cond, state)
          assert(Checker.stmtIsClosed(body, keys)._1)

          assert(blocksAreToplevel(stmt)._2 == 0)
          Interpreter.evalExpr(cond, state) match
            case Left(_) => () 
            case Right(c) =>
              if c then
                assert(Checker.stmtIsClosed(_Block(body), keySet((state.envs(0) :: state.envs)(0)))._1)
              else ()
        case Seq(stmt1, stmt2) =>
          assert(Checker.stmtIsClosed(stmt1, keys)._1)
          closedStmtEvalPlusClosedness1(stmt1, state, blocks)
          evalStmt1Consistency(stmt1, state, blocks)
          evalStmt1Aux(stmt1, state, blocks)

          assert(blocksAreToplevel(stmt2)._2 == 0)

          Interpreter.evalStmt1(stmt1, state, blocks) match
            case Left(b)     => ()
            case Right(conf) =>
              conf match
                case St(nstate)          =>
                  //assert(stateIsConsistent(nstate, blocks))
                  //assert(nstate.envs.size == blocks + 1)

                  val bl = blocksAreToplevel(stmt1)._2
                  assert(blocksAreToplevel(stmt)._2 == bl)

                  assert(Checker.stmtIsClosed(stmt1, keySet(state.envs(bl)))._2 == keySet(nstate.envs(0)))

                  assert(Checker.stmtIsClosed(stmt2, keySet(nstate.envs(0)))._1)
                case Cmd(nstmt1, nstate) =>
                  //assert(stmtAndStateAreConsistent(Seq(nstmt1, stmt2), nstate, blocks))
                  //assert(nstate.envs != Nil())

                  val bl = blocksAreToplevel(stmt1)._2
                  val nbl = blocksAreToplevel(nstmt1)._2

                  assert(Checker.stmtIsClosed(stmt1, keySet(state.envs(bl)))._2 == Checker.stmtIsClosed(nstmt1, keySet(nstate.envs(nbl)))._2)

                  //assert(Checker.stmtIsClosed(stmt2, keySet(nstate.envs(nbl)))._1)

                  //evalStmt1Aux(Seq(nstmt1, stmt2), nstate, blocks)

                  assert(blocksAreToplevel(Seq(nstmt1, stmt2))._2 == nbl)

                  assert(Checker.stmtIsClosed(Seq(nstmt1, stmt2), keySet(nstate.envs(nbl)))._1)
        case Free(name)        => ()
        case _Block(stmt0)     =>
          assert(Checker.stmtIsClosed(stmt0, keys)._1)
          closedStmtEvalPlusClosedness1(stmt0, state, blocks + 1)
          evalStmt1Consistency(stmt0, state, blocks + 1)

          Interpreter.evalStmt1(stmt0, state, blocks + 1) match
            case Left(b)     => ()
            case Right(conf) =>
              conf match
                case St(nstate)          =>
                  //assert(stateIsConsistent(nstate, blocks + 1))
                  //assert(nstate.envs.size == blocks + 2)
                  //assert(nstate.envs.tail.size == blocks + 1)
                case Cmd(nstmt0, nstate) =>

                  val bl = blocksAreToplevel(stmt0)._2
                  val nbl = blocksAreToplevel(nstmt0)._2

                  assert(Checker.stmtIsClosed(nstmt0, keySet(nstate.envs(nbl)))._1)
                  assert(Checker.stmtIsClosed(_Block(nstmt0), keySet(nstate.envs(nbl + 1)))._1)
                  //assert(stmtAndStateAreConsistent(nstmt0, nstate, blocks + 1))
                  //assert(stmtAndStateAreConsistent(_Block(nstmt0), nstate, blocks))
                  //assert(nstate.envs != Nil())
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      =>
          conf match
            case St(nstate)         => true
            case Cmd(nstmt, nstate) =>
              Checker.stmtIsClosed(nstmt, keySet(nstate.envs(blocksAreToplevel(nstmt)._2)))._1
        case Left(exceptions) =>
          !exceptions.contains(LangException.UndeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    def closedStmtEval(stmt: Stmt, state: State): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, 0))
      val keys = keySet(state.envs.head)
      require(Checker.stmtIsClosed(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, 0)
      closedStmtEvalPlusClosedness1(stmt, state, 0)
      Interpreter.evalStmt1(stmt, state, 0) match
        case Left(_)     => ()
        case Right(conf) =>
          conf match
            case St(nstate)         => ()
            case Cmd(nstmt, nstate) =>
              closedStmtEval(nstmt, nstate)
    }.ensuring(
      Interpreter.evalStmt(stmt, state) match
        case Right(fstate)    => true
        case Left(exceptions) =>
          !exceptions.contains(LangException.UndeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )
  }

  /*
  /** Lemmas and proofs of closedness: A program has no redeclarations if whenever evaluating
    * Decl〈name, expr〉, env(name) is not defined.
    */
  object NoRedeclarations {
    def hasNoRedeclarationsExprEval(expr: Expr, state: State): Unit = {
      require(state.envs.nonEmpty)
      val keys = keySet(state.envs.head)
      expr match
        case True              => ()
        case False             => ()
        case Ident(name)       => ()
        case Nand(left, right) =>
          hasNoRedeclarationsExprEval(left, state)
          hasNoRedeclarationsExprEval(right, state)
    }.ensuring(
      Interpreter.evalExpr(expr, state) match
        case Right(_)         => true
        case Left(exceptions) =>
          !exceptions.contains(LangException.RedeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    def evalStmt1Aux(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs.head)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)
      noRedeclStmtEvalPlusNoRedecl1(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          consistentKeySet(keys, state.envs.head, name, state.nextLoc)
        case Assign(to, value) => ()
        case If(cond, body)    => ()
        case Seq(stmt1, stmt2) =>
          Interpreter.evalStmt1(stmt1, state, blocks) match
            case Left(b)     => ()
            case Right(conf) =>
              conf match
                case St(nstate)          => ()
                case Cmd(nstmt1, nstate) =>
                  evalStmt1Aux(Seq(nstmt1, stmt2), nstate, blocks)
        case Free(name)        => ()
        case _Block(stmt0)     =>
          Interpreter.evalStmt1(stmt0, state, blocks + 1) match
            case Left(b)     => ()
            case Right(conf) =>
              conf match
                case St(nstate)          => ()
                case Cmd(nstmt0, nstate) =>
                  evalStmt1Aux(_Block(nstmt0), nstate, blocks)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Left(_)     => true
        case Right(conf) =>
          conf match
            case St(nstate)         =>
              stateIsConsistent(nstate, blocks) &&
              (Checker.stmtHasNoRedeclarations(stmt, keySet(state.envs.head))._2
                == keySet(nstate.envs.head))
            case Cmd(nstmt, nstate) =>
              stmtAndStateAreConsistent(nstmt, nstate, blocks) &&
              (Checker.stmtHasNoRedeclarations(stmt, keySet(state.envs.head))._2
                == Checker.stmtHasNoRedeclarations(nstmt, keySet(nstate.envs.head))._2)
    )

    def noRedeclStmtEvalPlusNoRedecl1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs.head)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)
      evalStmt1Aux(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          hasNoRedeclarationsExprEval(value, state)
        case Assign(to, value) =>
          hasNoRedeclarationsExprEval(value, state)
          keySetPost(state.envs.head, to)
        case If(cond, body)    =>
          hasNoRedeclarationsExprEval(cond, state)
        case Seq(stmt1, stmt2) =>
          noRedeclStmtEvalPlusNoRedecl1(stmt1, state, blocks)
        case Free(name)        => ()
        case _Block(stmt0)     =>
          noRedeclStmtEvalPlusNoRedecl1(stmt0, state, blocks + 1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      =>
          conf match
            case St(nstate)         =>
              stateIsConsistent(nstate, blocks)
            case Cmd(nstmt, nstate) =>
              stmtAndStateAreConsistent(nstmt, nstate, blocks)
              && Checker.stmtHasNoRedeclarations(nstmt, keySet(nstate.envs.head))._1
        case Left(exceptions) =>
          !exceptions.contains(LangException.RedeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    def noRedeclarationsStmtEval(stmt: Stmt, state: State): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, 0))
      val keys = keySet(state.envs.head)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, 0)
      noRedeclStmtEvalPlusNoRedecl1(stmt, state, 0)
      Interpreter.evalStmt1(stmt, state, 0) match
        case Left(_)     => ()
        case Right(conf) =>
          conf match
            case St(nstate)         => ()
            case Cmd(nstmt, nstate) =>
              noRedeclarationsStmtEval(nstmt, nstate)
    }.ensuring(
      Interpreter.evalStmt(stmt, state) match
        case Right(fstate)    => true
        case Left(exceptions) =>
          !exceptions.contains(LangException.RedeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )
  }

  /** Lemmas and proofs of unique ownership: A program exhibits unique ownership when env is
    * injective at all times.
    */
  object UniqueOwnership {

    /** The next free location variable (state.nextLoc) can only increase in value. */
    def locIncreases(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      decreases(stmt)
      stmt match
        case Decl(_, _)    =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => ()
            case Right(conf) =>
              conf match
                case St(nstate) =>
                  assert(nstate.nextLoc == state.nextLoc + 1)
                case Cmd(_, _)  => ()
        case Assign(_, _)  => ()
        case If(_, _)      => ()
        // case While(_, _)    => ()
        case Free(name)    => ()
        case Seq(stmt1, _) =>
          locIncreases(stmt1, state, blocks)
        case _Block(stmt1) =>
          locIncreases(stmt1, state, blocks + 1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Left(_)     => true
        case Right(conf) =>
          conf match
            case St(nstate)     => nstate.nextLoc >= state.nextLoc
            case Cmd(_, nstate) => nstate.nextLoc >= state.nextLoc
    )

    /* The next free location variable (state.nextLoc) can only
     * increase by one at every interpretation step. */
    def locIncreasesByOne(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      decreases(stmt)
      val State(scopes, mem, loc) = state

      require(!mem.contains(loc))
      stmt match
        case Decl(_, _)    =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => ()
            case Right(conf) =>
              conf match
                case St(nstate) =>
                  assert(nstate.nextLoc == state.nextLoc + 1)
                case Cmd(_, _)  => ()
        case Assign(_, _)  => ()
        case If(_, _)      => ()
        // case While(_, _)    => ()
        case Free(name)    => ()
        case Seq(stmt1, _) =>
          locIncreasesByOne(stmt1, state, blocks)
        case _Block(stmt1) =>
          locIncreasesByOne(stmt1, state, blocks + 1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Left(_)     => true
        case Right(conf) =>
          conf match
            case St(nstate)     =>
              nstate.nextLoc == state.nextLoc || nstate.nextLoc == state.nextLoc + 1
            case Cmd(_, nstate) =>
              nstate.nextLoc == state.nextLoc || nstate.nextLoc == state.nextLoc + 1
    )

    /* Loc increses by one with a declaration */
    def locIncreasesWithDecl(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      decreases(stmt)
      val State(scopes, mem, loc) = state
      stmt match
        case Decl(_, _)    =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => ()
            case Right(conf) =>
              conf match
                case St(nstate) =>
                  assert(nstate.nextLoc == state.nextLoc + 1)
                case Cmd(_, _)  => ()
        case Assign(_, _)  => ()
        case If(_, _)      => ()
        // case While(_, _)    => ()
        case Free(name)    => ()
        case Seq(stmt1, _) =>
          locIncreasesWithDecl(stmt1, state, blocks)
        case _Block(stmt1) =>
          locIncreasesWithDecl(stmt1, state, blocks + 1)
    }.ensuring(
      stmt match
        case Decl(name, value) =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => true
            case Right(conf) =>
              conf match
                case St(nstate)     =>
                  nstate.nextLoc == state.nextLoc + 1
                case Cmd(_, nstate) =>
                  nstate.nextLoc == state.nextLoc + 1
        case _                 => true
    )

    /* If a list of envs is updated with a name and the next free loc,
     * the top env contains name and name is mapped to the previous next
     * free loc */
    def envListUpdated(state: State, x: Name): List[Env] = {
      require(state.envs.nonEmpty)
      val nenv = state.envs.head + (x -> state.nextLoc)
      :: state.envs.tail
      nenv
    }.ensuring(r => (r.head contains x) && r.head(x) == state.nextLoc)

    def envListEquality(env1: List[Env], env2: List[Env], x: Name, l: Loc): Unit = {
      require(env1.nonEmpty && env2.nonEmpty)
      require(env1.head == env2.head)
      require(!(env1.head contains x))
      require(!(env2.head contains x))
    }.ensuring(env1.head == (env2.head + (x -> l)) - x)

    /* Declarations always allocate using the next free location (state.nextLoc) */
    def declUsesNextLoc(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      stmt match
        case Decl(name, value) =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => ()
            case Right(conf) =>
              conf match
                case St(nstate) =>
                  envListUpdated(state, name)
                  assert(nstate.envs.head contains name) // new var in previous loc
                  assert(nstate.envs.head(name) == state.nextLoc) // new var in previous loc
                case Cmd(_, _)  => ()
        case Assign(_, _)      => ()
        case If(_, _)          => ()
        // case While(_, _)        => ()
        case Seq(stmt1, _)     =>
          declUsesNextLoc(stmt1, state, blocks)
        case Free(name)        => ()
        case _Block(stmt1)     =>
          declUsesNextLoc(stmt1, state, blocks + 1)
    }.ensuring(
      stmt match
        case Decl(name, value) =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => true
            case Right(conf) =>
              conf match
                case St(nstate)     =>
                  nstate.envs.head(name) == state.nextLoc // new var in previous loc
                case Cmd(_, nstate) =>
                  nstate.envs.head(name) == state.nextLoc
        case _                 => true
    )

    /* Next free location never in memory */
    // TODO: Improve precodition: every loc greater than next loc is not in memory
    def nextLocNeverInMemory(stmt: Stmt, state: State, blocks: BigInt, v: Boolean): Unit = {
      require(!(state.mem contains state.nextLoc))
      require(!(state.mem contains state.nextLoc + 1))
      require(!(state.mem contains state.nextLoc + 2))
      stmt match
        case Decl(_, _)    =>
          Interpreter.evalStmt1(stmt, state, blocks) match
            case Left(_)     => ()
            case Right(conf) =>
              conf match
                case St(nstate) =>
                  assert(!(nstate.mem contains nstate.nextLoc))
                case Cmd(_, _)  => ()
        case Assign(_, _)  => ()
        case If(_, _)      => ()
        // case While(_, _)    => ()
        case Seq(stmt1, _) =>
          nextLocNeverInMemory(stmt1, state, blocks, v)
        case Free(name)    => ()
        case _Block(stmt1) =>
          nextLocNeverInMemory(stmt1, state, blocks + 1, v)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Left(_)     => true
        case Right(conf) =>
          conf match
            case St(nstate)     =>
              !(nstate.mem contains nstate.nextLoc)
            case Cmd(_, nstate) =>
              !(nstate.mem contains nstate.nextLoc)
    )
  }

  /* If map contains x, if x is updated in the map the number of keys preserved */
  @extern @pure
  def mapsUpdate(map: Mem, x: Loc, y: Boolean): Unit = {
    require(map.contains(x))
  }.ensuring(_ => map.updated(x, y).keys == map.keys)

  /* Two equal maps have the same number of keys */
  def equalKeyCardinality[K, V](map1: Map[K, V], map2: Map[K, V]): Unit = {
    require(map1 == map2)
  }.ensuring(map1.keys.length == map2.keys.length)

  /* If map1 is equal to map2 - k, then map2 has one key more than map1 */
  @extern @pure
  def equalKeyCardinalityIncrement[K, V](map1: Map[K, V], map2: Map[K, V], k: K): Unit = {
    require(map1 == map2 - k)
    require(map2 contains k)
  }.ensuring(map1.keys.length + 1 == map2.keys.length)

  /* If map1 is equal to map2 and map2 is updated with a new key,
   * then the updated map2 has one key more than map1 */
  @extern @pure
  def greaterKeyCardinality[K, V](map1: Map[K, V], map2: Map[K, V], k: K, v: V): Unit = {
    require(map1 == map2)
    require(!(map2 contains k))
    require(!(map1 contains k))
    equalKeyCardinality(map1, map2)
  }.ensuring(map1.keys.length + 1 == (map2 + (k -> v)).keys.length)

  /* If map1 and map2 have the same length and contain k,
   * if k is updated in map2 then the number of keys is preserved */
  @extern @pure
  def equalKeyCardUpdateCommonKey[K, V](map1: Map[K, V], map2: Map[K, V], k: K, v: V): Unit = {
    // require(map1 == map2)
    require(map1.keys.length == map2.keys.length)
    require(map1 contains k)
    require(map2 contains k)
  }.ensuring(map1.keys.length == (map2 + (k -> v)).keys.length)

  /* If map1 and map2 have the same length and do not contain k,
   * if k is added in both maps then the number of keys is still equal */
  @extern @pure
  def equalKeyCardPreserved[K, V](map1: Map[K, V], map2: Map[K, V], k: K, v1: V, v2: V): Unit = {
    require(map1.keys.length == map2.keys.length)
    require(!(map1 contains k))
    require(!(map2 contains k))
  }.ensuring((map1 + (k -> v1)).keys.length == (map2 + (k -> v2)).keys.length)

  /* At every interpretation step, memory can only increase by one. */
  def memIncreasesByOne(stmt: Stmt, state: State, blocks: BigInt, v: Boolean): Unit = {
    val State(scopes, mem, loc) = state
    require(!(mem contains loc))
    stmt match
      case Decl(name, _) =>
        Interpreter.evalStmt1(stmt, state, blocks) match
          case Left(_)     => ()
          case Right(conf) =>
            conf match
              case St(nstate)     =>
                assert(nstate.mem - (loc) == state.mem) // VALID
                equalKeyCardinalityIncrement(state.mem, nstate.mem, loc)
                assert(state.mem.keys.length + 1 == nstate.mem.keys.length)
              case Cmd(_, nstate) =>
                assert(nstate.mem == state.mem)
                equalKeyCardinality(state.mem, nstate.mem)
                assert(state.mem.keys.length == nstate.mem.keys.length)
      case Assign(to, _) =>
        Interpreter.evalStmt1(stmt, state, blocks) match
          case Left(_)     => ()
          case Right(conf) =>
            conf match
              case St(nstate)     =>
                val toLoc = state.envs.head(to)
                equalKeyCardPreserved(
                  state.mem - toLoc,
                  nstate.mem - toLoc,
                  toLoc,
                  state.mem(toLoc),
                  nstate.mem(toLoc)
                )
                assert(nstate.mem - toLoc == state.mem - toLoc)
                equalKeyCardUpdateCommonKey(state.mem, state.mem, toLoc, v)
                assert(state.mem.keys.length == nstate.mem.keys.length)
              case Cmd(_, nstate) =>
                assert(nstate.mem == state.mem)
                equalKeyCardinality(state.mem, nstate.mem)
                assert(state.mem.keys.length == nstate.mem.keys.length)
      case If(_, _)      =>
        Interpreter.evalStmt1(stmt, state, blocks) match
          case Left(_)     => ()
          case Right(conf) =>
            conf match
              case St(nstate)     =>
                assert(nstate.mem == state.mem)
                equalKeyCardinality(state.mem, nstate.mem)
                assert(state.mem.keys.length == nstate.mem.keys.length)
              case Cmd(_, nstate) =>
                assert(nstate.mem == state.mem)
                equalKeyCardinality(state.mem, nstate.mem)
                assert(state.mem.keys.length == nstate.mem.keys.length)
      /*
      case While(_, _) =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case nstate:State =>
              assert(nstate.mem == state.mem)
              equalKeyCardinality(state.mem, nstate.mem)
              assert(state.mem.keys.length == nstate.mem.keys.length)
            case Cmd(_, nstate) =>
              assert(nstate.mem == state.mem)
              equalKeyCardinality(state.mem, nstate.mem)
              assert(state.mem.keys.length == nstate.mem.keys.length)
       */
      case Free(name)    => ()
      case Seq(stmt1, _) =>
        memIncreasesByOne(stmt1, state, blocks, v)
      case _Block(stmt1) =>
        memIncreasesByOne(stmt1, state, blocks + 1, v)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_)     => true
      case Right(conf) =>
        conf match
          case St(nstate)     =>
            nstate.mem.keys.length == state.mem.keys.length ||
            nstate.mem.keys.length == state.mem.keys.length + 1
          case Cmd(_, nstate) =>
            nstate.mem.keys.length == state.mem.keys.length ||
            nstate.mem.keys.length == state.mem.keys.length + 1
  )
  */

}
