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

  // The stack of envs is monotonic with regards to the subset relation.
  private def envStackInclusion(env: Env, envs: List[Env]): Boolean = envs match
    case Cons(h, t) => keySet(h).subsetOf(keySet(env)) && envStackInclusion(h, t)
    case Nil()      => true

  // Counting and validating the amount of synthetic _Blocks in the AST.
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

  // The consistency of the amount of blocks with relation to the stack of envs is maintained.
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

  // Proof that this consistency is indeed maintained.
  def evalStmt1Consistency(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, blocks))
    stmt match
      case Decl(name, value) =>
        subsetTest(state.envs.head, name, state.nextLoc)

        assert((state.envs.head + (name -> state.nextLoc) :: state.envs.tail).size == blocks + 1)
      case Seq(stmt1, stmt2) =>
        evalStmt1Consistency(stmt1, state, blocks)

        Interpreter.evalStmt1(stmt1, state, blocks) match
          case Left(content) => ()
          case Right(conf)   =>
            conf match
              case St(nstate)          =>
                assert(stateIsConsistent(nstate, blocks))
                assert(stmtAndStateAreConsistent(stmt2, nstate, blocks))
              case Cmd(nstmt1, nstate) =>
                assert(stmtAndStateAreConsistent(nstmt1, nstate, blocks))
                assert(stmtAndStateAreConsistent(Seq(nstmt1, stmt2), nstate, blocks))
      case _Block(stmt0)     =>
        evalStmt1Consistency(stmt0, state, blocks + 1)

        Interpreter.evalStmt1(stmt0, state, blocks + 1) match
          case Left(content) => ()
          case Right(conf)   =>
            conf match
              case St(nstate)          =>
                assert(stateIsConsistent(nstate, blocks + 1))
                assert(nstate.envs.size == blocks + 2)
                assert(nstate.envs.tail.size == blocks + 1)
                assert(envStackInclusion(nstate.envs.tail.head, nstate.envs.tail.tail))
              case Cmd(nstmt0, nstate) =>
                assert(stmtAndStateAreConsistent(nstmt0, nstate, blocks + 1))
                assert(stmtAndStateAreConsistent(_Block(nstmt0), nstate, blocks))
      case Assign(to, value) =>
        assert(state.envs.size == blocks + 1)
      case If(cond, body)    =>
        assert(state.envs.size == blocks + 1)
      case Free(name)        =>
        assert(state.envs.size == blocks + 1)
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_)     => true
      case Right(conf) =>
        conf match
          case St(nstate)         => stateIsConsistent(nstate, blocks)
          case Cmd(nstmt, nstate) => stmtAndStateAreConsistent(nstmt, nstate, blocks)
  )

  /** Lemmas and proofs of the internal interpreter property of no empty env stack
    */
  object _NoEmptyEnvStack {
    // Exception doesn't happen for expressions.
    def noEmptyEnvStackExprEval(expr: Expr, state: State): Unit = {
      require(state.envs.nonEmpty)
      expr match
        case True              => ()
        case False             => ()
        case Nand(left, right) =>
          noEmptyEnvStackExprEval(left, state)
          noEmptyEnvStackExprEval(right, state)
        case Ident(name)       => ()
    }.ensuring(
      Interpreter.evalExpr(expr, state) match
        case Right(_)         => true
        case Left(exceptions) => !exceptions.contains(LangException._EmptyEnvStack)
    )

    // Exception doesn't happen for statements.
    def noEmptyStackStmtEval1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      evalStmt1Consistency(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          noEmptyEnvStackExprEval(value, state)
        case Assign(to, value) =>
          noEmptyEnvStackExprEval(value, state)
        case If(cond, body)    =>
          noEmptyEnvStackExprEval(cond, state)
        case Seq(stmt1, stmt2) =>
          noEmptyStackStmtEval1(stmt1, state, blocks)
        case Free(name)        => ()
        case _Block(stmt0)     =>
          noEmptyStackStmtEval1(stmt0, state, blocks + 1)
          evalStmt1Consistency(stmt0, state, blocks + 1)
          Interpreter.evalStmt1(stmt0, state, blocks + 1) match
            case Left(b)     =>
              assert(!b.contains(LangException._EmptyEnvStack))
            case Right(conf) =>
              conf match
                case St(nstate)          =>
                  assert(nstate.envs.size == blocks + 2)
                  assert(nstate.envs.tail.size == blocks + 1)
                case Cmd(nstmt0, nstate) => ()
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      => true
        case Left(exceptions) => !exceptions.contains(LangException._EmptyEnvStack)
    )
  }

  // ---

  /** Lemmas and proofs of closedness: A program is closed if whenever evaluating Ident〈name〉,
    * Free〈name〉, or Assign〈name, expr〉, env(name) is defined.
    */
  object Closedness {
    // Exception doesn't happen for expressions.
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
        case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
    )

    // Exception doesn't happen for statements.
    def closedStmtEval1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs.head)
      require(Checker.stmtIsClosed(stmt, keys)._1)

      evalStmt1Consistency(stmt, state, blocks)

      stmt match
        case Decl(name, value) =>
          closedExprEval(value, state)
        case Assign(to, value) =>
          closedExprEval(value, state)
          keySetPost(state.envs.head, to)
          assert(state.envs.head.contains(to))
        case If(cond, body)    =>
          assert(Checker.exprIsClosed(cond, keys))
          closedExprEval(cond, state)
        case Seq(stmt1, stmt2) =>
          closedStmtEval1(stmt1, state, blocks)
        case Free(name)        =>
          keySetPost(state.envs.head, name)
          assert(state.envs.head.contains(name))
        case _Block(stmt0)     =>
          closedStmtEval1(stmt0, state, blocks + 1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(_)         => true
        case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
    )

    // Given a closed statement, a step of the tracer will maintain closedness.
    // TODO: the previous proof worked, but was very nondeterministic (stainless sometimes did and
    // sometimes did not accept the proof)
    @extern @pure
    def evalStmt1Closedness(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs.head)
      require(Checker.stmtIsClosed(stmt, keys)._1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      =>
          conf match
            case St(nstate)         => true
            case Cmd(nstmt, nstate) =>
              nstate.envs.size > 0 && Checker.stmtIsClosed(nstmt, keySet(nstate.envs.head))._1
        case Left(exceptions) => true
    )

    // Evaluating the whole program will not produce the UndeclaredVariable exception.
    def closedStmtEval(stmt: Stmt, state: State): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, 0))
      val keys = keySet(state.envs.head)
      require(Checker.stmtIsClosed(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, 0)
      closedStmtEval1(stmt, state, 0)
      evalStmt1Closedness(stmt, state, 0)
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
        case Left(exceptions) => !exceptions.contains(LangException.UndeclaredVariable)
    )
  }

  /** Lemmas and proofs of closedness: A program has no redeclarations if whenever evaluating
    * Decl〈name, expr〉, env(name) is not defined.
    */
  object NoRedeclarations {
    // Exception doesn't happen for expressions.
    def noRedeclarationsExprEval(expr: Expr, state: State): Unit = {
      require(state.envs.nonEmpty)
      expr match
        case True              => ()
        case False             => ()
        case Ident(name)       => ()
        case Nand(left, right) =>
          noRedeclarationsExprEval(left, state)
          noRedeclarationsExprEval(right, state)
    }.ensuring(
      Interpreter.evalExpr(expr, state) match
        case Right(_)         => true
        case Left(exceptions) => !exceptions.contains(LangException.RedeclaredVariable)
    )

    // Exception doesn't happen for statements.
    def noRedeclarationsStmtEval1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs.head)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)

      evalStmt1Consistency(stmt, state, blocks)

      stmt match
        case Decl(name, value) =>
          noRedeclarationsExprEval(value, state)
          keySetPost(state.envs.head, name)
        case Assign(to, value) =>
          noRedeclarationsExprEval(value, state)
          keySetPost(state.envs.head, to)
        case If(cond, body)    =>
          noRedeclarationsExprEval(cond, state)
        case Seq(stmt1, stmt2) =>
          noRedeclarationsStmtEval1(stmt1, state, blocks)
          evalStmt1Consistency(stmt1, state, blocks)
          Interpreter.evalStmt1(stmt1, state, blocks) match
            case Left(content) => ()
            case Right(conf)   =>
              conf match
                case St(nstate)          =>
                  assert(stateIsConsistent(nstate, blocks))
                case Cmd(nstmt1, nstate) =>
                  assert(stmtAndStateAreConsistent(nstmt1, nstate, blocks))
        case Free(name)        =>
          keySetPost(state.envs.head, name)
        case _Block(stmt0)     =>
          noRedeclarationsStmtEval1(stmt0, state, blocks + 1)
          evalStmt1Consistency(stmt0, state, blocks + 1)
          Interpreter.evalStmt1(stmt0, state, blocks + 1) match
            case Left(content) => assert(!content.contains(LangException.RedeclaredVariable))
            case Right(conf)   =>
              conf match
                case St(nstate)          =>
                  assert(stateIsConsistent(nstate, blocks + 1))
                  assert(nstate.envs.size == blocks + 2)
                  assert(nstate.envs.tail.size == blocks + 1)
                  assert(envStackInclusion(nstate.envs.tail.head, nstate.envs.tail.tail))
                case Cmd(nstmt0, nstate) =>
                  assert(stmtAndStateAreConsistent(nstmt0, nstate, blocks + 1))
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      => true
        case Left(exceptions) =>
          !exceptions.contains(LangException.RedeclaredVariable)
    )

    // Given a statement with no redeclarations, a step of the tracer will maintain lack of redeclarations.
    // TODO: the previous proof worked, but was very nondeterministic (stainless sometimes did and
    // sometimes did not accept the proof)
    @extern @pure
    def evalStmt1NoRedeclarations(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.envs.head)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      =>
          conf match
            case St(nstate)         => true
            case Cmd(nstmt, nstate) =>
              nstate.envs.size > 0 &&
              Checker.stmtHasNoRedeclarations(nstmt, keySet(nstate.envs.head))._1
        case Left(exceptions) => true
    )

    // Evaluating the whole program will not produce the RedeclaredVariable exception.
    def noRedeclarationsStmtEval(stmt: Stmt, state: State): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, 0))
      val keys = keySet(state.envs.head)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, 0)
      noRedeclarationsStmtEval1(stmt, state, 0)
      evalStmt1NoRedeclarations(stmt, state, 0)
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
        case Left(exceptions) => !exceptions.contains(LangException.RedeclaredVariable)
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
      val State(envs, mem, freed, loc) = state

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
      val State(envs, mem, freed, loc) = state
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
      val nenv = state.envs.head + (x -> state.nextLoc) :: state.envs.tail
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
}
