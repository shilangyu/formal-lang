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

  private def envStackInclusion(env: Env, scopes: List[Scope]): Boolean = scopes match
    case Cons(h, t) => keySet(h.env).subsetOf(keySet(env)) && envStackInclusion(h.env, t)
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
    blocks >= 0 && b && i + blocks + 1 == state.scopes.size && envStackInclusion(
      state.scopes.head.env,
      state.scopes.tail
    )

  def stateIsConsistent(state: State, blocks: BigInt): Boolean =
    blocks >= 0 && blocks + 1 == state.scopes.size && envStackInclusion(
      state.scopes.head.env,
      state.scopes.tail
    )

  def evalStmt1Consistency(stmt: Stmt, state: State, blocks: BigInt): Unit = {
    require(stmtAndStateAreConsistent(stmt, state, blocks))
    stmt match
      case Decl(name, value) =>
        subsetTest(state.scopes.head.env, name, state.nextLoc)
      case Seq(stmt1, stmt2) =>
        evalStmt1Consistency(stmt1, state, blocks)
      case _Block(stmt0)     =>
        evalStmt1Consistency(stmt0, state, blocks + 1)
      case _                 => ()
  }.ensuring(
    Interpreter.evalStmt1(stmt, state, blocks) match
      case Left(_)     => true
      case Right(conf) =>
        conf match
          case St(nstate)         => stateIsConsistent(nstate, blocks)
          case Cmd(nstmt, nstate) => stmtAndStateAreConsistent(nstmt, nstate, blocks)
  )

  // ---

  /** Lemmas and proofs of closedness: A program is closed if whenever evaluating Ident〈name〉 or
    * Assign〈name, expr〉, env(name) is defined.
    */
  object Closedness {
    def closedExprEval(expr: Expr, state: State): Unit = {
      require(state.scopes.nonEmpty)
      val keys = keySet(state.scopes.head.env)
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
          keySetPost(state.scopes.head.env, name)
          assert(state.scopes.head.env.contains(name))
    }.ensuring(
      Interpreter.evalExpr(expr, state) match
        case Right(_)         => true
        case Left(exceptions) =>
          !exceptions.contains(LangException.UndeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    def evalStmt1Aux(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.scopes.head.env)
      require(Checker.stmtIsClosed(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)
      closedStmtEvalPlusClosedness1(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          consistentKeySet(keys, state.scopes.head.env, name, state.nextLoc)
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
              (Checker.stmtIsClosed(stmt, keySet(state.scopes.head.env))._2
                == keySet(nstate.scopes.head.env))
            case Cmd(nstmt, nstate) =>
              stmtAndStateAreConsistent(nstmt, nstate, blocks) &&
              (Checker.stmtIsClosed(stmt, keySet(state.scopes.head.env))._2
                == Checker.stmtIsClosed(nstmt, keySet(nstate.scopes.head.env))._2)
    )

    def closedStmtEvalPlusClosedness1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.scopes.head.env)
      require(Checker.stmtIsClosed(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)
      evalStmt1Aux(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          closedExprEval(value, state)
        case Assign(to, value) =>
          closedExprEval(value, state)
          keySetPost(state.scopes.head.env, to)
        case If(cond, body)    =>
          closedExprEval(cond, state)
        case Seq(stmt1, stmt2) =>
          closedStmtEvalPlusClosedness1(stmt1, state, blocks)
        case Free(name)        => ()
        case _Block(stmt0)     =>
          closedStmtEvalPlusClosedness1(stmt0, state, blocks + 1)
    }.ensuring(
      Interpreter.evalStmt1(stmt, state, blocks) match
        case Right(conf)      =>
          conf match
            case St(nstate)         =>
              stateIsConsistent(nstate, blocks)
            case Cmd(nstmt, nstate) =>
              stmtAndStateAreConsistent(nstmt, nstate, blocks)
              && Checker.stmtIsClosed(nstmt, keySet(nstate.scopes.head.env))._1
        case Left(exceptions) =>
          !exceptions.contains(LangException.UndeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    def closedStmtEval(stmt: Stmt, state: State): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, 0))
      val keys = keySet(state.scopes.head.env)
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

  /** Lemmas and proofs of closedness: A program has no redeclarations if whenever evaluating
    * Decl〈name, expr〉, env(name) is not defined.
    */
  object NoRedeclarations {
    def hasNoRedeclarationsExprEval(expr: Expr, state: State): Unit = {
      require(state.scopes.nonEmpty)
      val keys = keySet(state.scopes.head.env)
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
      val keys = keySet(state.scopes.head.env)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)
      noRedeclStmtEvalPlusNoRedecl1(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          consistentKeySet(keys, state.scopes.head.env, name, state.nextLoc)
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
              (Checker.stmtHasNoRedeclarations(stmt, keySet(state.scopes.head.env))._2
                == keySet(nstate.scopes.head.env))
            case Cmd(nstmt, nstate) =>
              stmtAndStateAreConsistent(nstmt, nstate, blocks) &&
              (Checker.stmtHasNoRedeclarations(stmt, keySet(state.scopes.head.env))._2
                == Checker.stmtHasNoRedeclarations(nstmt, keySet(nstate.scopes.head.env))._2)
    )

    def noRedeclStmtEvalPlusNoRedecl1(stmt: Stmt, state: State, blocks: BigInt): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, blocks))
      val keys = keySet(state.scopes.head.env)
      require(Checker.stmtHasNoRedeclarations(stmt, keys)._1)
      evalStmt1Consistency(stmt, state, blocks)
      evalStmt1Aux(stmt, state, blocks)
      stmt match
        case Decl(name, value) =>
          hasNoRedeclarationsExprEval(value, state)
        case Assign(to, value) =>
          hasNoRedeclarationsExprEval(value, state)
          keySetPost(state.scopes.head.env, to)
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
              && Checker.stmtHasNoRedeclarations(nstmt, keySet(nstate.scopes.head.env))._1
        case Left(exceptions) =>
          !exceptions.contains(LangException.RedeclaredVariable)
          && !exceptions.contains(LangException._EmptyScopeStack)
    )

    def noRedeclarationsStmtEval(stmt: Stmt, state: State): Unit = {
      require(stmtAndStateAreConsistent(stmt, state, 0))
      val keys = keySet(state.scopes.head.env)
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
    def envListUpdated(state: State, x: Name): List[Scope] = {
      require(state.scopes.nonEmpty)
      val nenv = Scope(
        state.scopes.head.env + (x -> state.nextLoc),
        state.scopes.head.freed
      ) :: state.scopes.tail
      nenv
    }.ensuring(r => (r.head.env contains x) && r.head.env(x) == state.nextLoc)

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
                  assert(nstate.scopes.head.env contains name) // new var in previous loc
                  assert(nstate.scopes.head.env(name) == state.nextLoc) // new var in previous loc
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
                  nstate.scopes.head.env(name) == state.nextLoc // new var in previous loc
                case Cmd(_, nstate) =>
                  nstate.scopes.head.env(name) == state.nextLoc
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
}
