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
      case True               => ()
      case False              => ()
      case Nand(left, right)  =>
        assert(Checker.isExprClosed(left, env))
        assert(Checker.isExprClosed(right, env))
        closedExprEvaluates(left, state)
        closedExprEvaluates(right, state)
      case Ident(name)        =>
        assert(env.contains(name))
  }.ensuring(
    Interpreter.evalExpr(expr, state) match
      case Right(_)         => true
      case Left(exceptions) => 
        !exceptions.contains(LangException.UndeclaredVariable)
  )

  /* if the program is closed then the Interpreter will not 
   * throw UndeclaredVariable exception. */
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
      case Block(stmt1)       =>
        closedStmtNoUndeclaredVar(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Right(_)         => true
      case Left(exceptions) => 
        !exceptions.contains(LangException.UndeclaredVariable)
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
        closedStmtNoUndeclaredVar(body, (env.push(env.head), state._2, state._3))
        closenessIsPreserved(body, (env.push(env.head), state._2, state._3))
      case While(cond, body)     =>
        assert(Checker.isExprClosed(cond, env.head))
        closedExprEvaluates(cond, state)
        closedStmtNoUndeclaredVar(body, (env.push(env.head), state._2, state._3))
        closenessIsPreserved(body, (env.push(env.head), state._2, state._3))
      case Seq(stmt1, stmt2)      => //stmt1 match
        Interpreter.traceStmt1(stmt1, state) match
          case Right(conf) => conf match
            case St(nstate) => 
              assert(!stmt1.isInstanceOf[Block])
              closenessIsPreserved(stmt2, nstate)
            case Cmd(nstmt1, nstate) => 
              //assert(Checker.isStmtClosed(nstmt1, nstate._1)._1)    
              //assert(!stmt1.isInstanceOf[Block])
              closedStmtNoUndeclaredVar(stmt1, state)
              closenessIsPreserved(stmt1, nstate)
              //closenessIsPreserved(nstmt1, nstate)
              //closenessIsPreserved(Seq(nstmt1,stmt2), nstate)
          case Left(_) => ()
        Interpreter.traceStmt1(stmt, state) match
          case Right(conf) => conf match
            case St(nstate) => ()
            case Cmd(nstmt, nstate) => 
              //assert(Checker.isStmtClosed(nstmt1, nstate._1)._1)    
              closenessIsPreserved(nstmt, nstate)
              //closenessIsPreserved(Seq(nstmt1,stmt2), nstate)
          case Left(_) => ()

        /*
        case Decl(_, _) => ()
        case Assign(_, _) => ()
        case If(_, _) => ()
        case While(_, _) => ()
        case Seq(_, _) =>
          closenessIsPreserved(stmt1, state)    // valid
          Interpreter.traceStmt1(stmt1, state) match
            case Right(conf) => conf match
              case St(nstate) => ()
              case Cmd(nstmt1, nstate) => 
                assert(Checker.isStmtClosed(nstmt1, nstate._1)._1)    // valid
                closenessIsPreserved(nstmt1, nstate)
                closenessIsPreserved(Seq(nstmt1,stmt2), nstate)
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
                //assert(Checker.isStmtClosed(nstmt1, state1._1)._1)
            case Left(_) => ()
            */
        closedStmtNoUndeclaredVar(stmt1, state)
        Interpreter.traceStmt1(stmt, state) match
          case Right(conf) => conf match
            case St(state1) => ()
            case Cmd(nstmt1, state1) => 
              assert(Checker.isStmtClosed(nstmt1, state1._1)._1)
          case Left(_) => ()
      case Block(stmt1)  =>
        closedStmtNoUndeclaredVar(stmt1, state)
        closenessIsPreserved(stmt1, state)
      /*
      case Block(true, stmt1)   =>
        assert(env.head == env.push(env.head).head)
        assert(Checker.isStmtClosed(stmt1, env.push(env.head))._1)
        closedStmtNoUndeclaredVar(stmt1, (env.push(env.head), state._2, state._3))
        closenessIsPreserved(stmt1, (env.push(env.head), state._2, state._3))
      case Block(false, stmt1)  =>
        closedStmtNoUndeclaredVar(stmt1, state)
        closenessIsPreserved(stmt1, state)
        */
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

  /* The next free location variable (state._3) can only increase in value. */
  def locIncreases(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val env = state._1
    stmt match
      case Decl(_, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._3 == state._3 + 1)
            case Cmd(_, _)  => ()
      case Assign(_, _)   => ()
      case If(_, _)       => () 
      case While(_, _)    => ()
      case Seq(stmt1, _)  => 
        locIncreases(stmt1, state)
      case Block(stmt1)   => 
        locIncreases(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(nstate) => nstate._3 >= state._3
        case Cmd(_, nstate) => nstate._3 >= state._3
    )

  /* The next free location variable (state._3) can only 
   * increase by one at every interpretation step. */
  def locIncreasesByOne(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val env = state._1
    val mem = state._2
    val loc = state._3
    require(!mem.contains(loc))
    stmt match
      case Decl(_, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._3 == state._3 + 1)
            case Cmd(_, _)  => ()
      case Assign(_, _)   => ()
      case If(_, _)       => () 
      case While(_, _)    => ()
      case Seq(stmt1, _)  => 
        locIncreasesByOne(stmt1, state)
      case Block(stmt1)   => 
        locIncreasesByOne(stmt1, state)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(nstate) => 
          nstate._3 == state._3 || nstate._3 == state._3 + 1
        case Cmd(_, nstate) => 
          nstate._3 == state._3 || nstate._3 == state._3 + 1
    )

  /* Loc increses by one with a declaration */
  def locIncreasesWithDecl(stmt: Stmt, state: State): Unit = {
    decreases(stmt)
    val env = state._1
    val mem = state._2
    val loc = state._3
    stmt match
      case Decl(_, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._3 == state._3 + 1)
            case Cmd(_, _)  => ()
      case Assign(_, _)   => ()
      case If(_, _)       => () 
      case While(_, _)    => ()
      case Seq(stmt1, _)  => 
        locIncreasesWithDecl(stmt1, state)
      case Block(stmt1)   => 
        locIncreasesWithDecl(stmt1, state)
  }.ensuring(
    stmt match
      case Decl(name, value) => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => true
          case Right(conf)  => conf match
            case St(nstate) =>
              nstate._3 == state._3 + 1
            case Cmd(_, nstate) =>
              nstate._3 == state._3 + 1
      case _ => true
    )

  def envListUpdated(state: State, name: Name): EnvList = {
    val nenv = state._1.tail.push(state._1.head + (name -> state._3))
    nenv
  }.ensuring(r => (r.head contains name) && r.head(name) == state._3)

  /* Declarations always allocate using the next free location (state._3) */
  def declUsesLoc(stmt: Stmt, state: State): Unit = {
    stmt match
      case Decl(name, value)  => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              envListUpdated(state, name)
              assert(nstate._1.head contains name)      // new var in previous loc
              assert(nstate._1.head(name) == state._3)  // new var in previous loc
            case Cmd(_, _) => ()
      case Assign(_, _)       => ()
      case If(_, _)           => () 
      case While(_, _)        => ()
      case Seq(stmt1, _)      =>
        declUsesLoc(stmt1, state)
      case Block(stmt1)       =>
        declUsesLoc(stmt1, state)
  }.ensuring(
    stmt match
      case Decl(name, value) => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => true
          case Right(conf)  => conf match
            case St(nstate) =>
              nstate._1.head(name) == state._3 // new var in previous loc
            case Cmd(_, nstate) =>
              nstate._1.head(name) == state._3
      case _ => true
    )

  @extern @pure
  def noNewLocsInMem(state: State, x: BigInt): Unit = {
    require(x >= 0)
  }.ensuring(!(state._2 contains state._3 + x))

  def newLocNeverInMemory(stmt: Stmt, state: State, v: Boolean): Unit = {
    require(!(state._2 contains state._3))
    require(!(state._2 contains state._3 + 1))
    require(!(state._2 contains state._3 + 2))
    stmt match
      case Decl(_, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(!(nstate._2 contains nstate._3))  
            case Cmd(_, _)  => ()
      case Assign(_, _)   => ()
      case If(_, _)       => () 
      case While(_, _)    => ()
      case Seq(stmt1, _)  => 
        newLocNeverInMemory(stmt1, state, /*x,*/ v)
      case Block(stmt1)   => 
        newLocNeverInMemory(stmt1, state, /*x,*/ v)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_) => true
      case Right(conf) => conf match
        case St(nstate) => 
          !(nstate._2 contains nstate._3)
        case Cmd(_, nstate) => 
          !(nstate._2 contains nstate._3)
    )

  @extern @pure
  def mapsUpdate(map: Mem, x: Loc, y: Boolean): Unit = {
    require(map.contains(x))
  }.ensuring(_ => map.updated(x, y).keys == map.keys)

  def equalKeyCardinality[K, V](map1: Map[K, V], map2: Map[K, V]): Unit  = {
    require(map1 == map2)
  }.ensuring(map1.keys.length == map2.keys.length)

  @extern @pure
  def equalKeyCardinalityIncrement[K, V](map1: Map[K, V], map2: Map[K, V], k: K): Unit  = {
    require(map1 == map2 - k)
    require(map2 contains k)
  }.ensuring(map1.keys.length + 1 == map2.keys.length)

  @extern @pure
  def greaterKeyCardinality[K, V](map1: Map[K, V], map2: Map[K, V], k: K, v: V): Unit  = {
    require(map1 == map2)
    require(!(map2 contains k))
    require(!(map1 contains k))
    equalKeyCardinality(map1, map2)
  }.ensuring(map1.keys.length + 1 == (map2 + (k -> v)).keys.length)

  @extern @pure
  def equalKeyCardUpdateCommonKey[K, V](map1: Map[K, V], map2: Map[K, V], k: K, v: V): Unit  = {
    //require(map1 == map2)
    require(map1.keys.length == map2.keys.length)
    require(map1 contains k)
    require(map2 contains k)
  }.ensuring(map1.keys.length == (map2 + (k -> v)).keys.length)

  @extern @pure
  def equalKeyCardPreserved[K, V](map1: Map[K, V], map2: Map[K, V], k: K, v1: V, v2: V): Unit  = {
    require(map1.keys.length == map2.keys.length)
    require(!map1.contains(k))
    require(!map2.contains(k))

  }.ensuring((map1 + (k -> v1)).keys.length == (map2 + (k -> v2)).keys.length)

  /* At every interpretation step, memory can only increase by one. */
  def memIncreasesByOne(stmt: Stmt, state: State, v: Boolean): Unit = {
    val env = state._1
    val mem = state._2
    val loc = state._3
    require(!mem.contains(loc))
    stmt match
      case Decl(name, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._2 - (loc) == state._2)    // VALID
              equalKeyCardinalityIncrement(state._2, nstate._2, loc)
              assert(state._2.keys.length + 1 == nstate._2.keys.length)
            case Cmd(_, nstate) => 
              assert(nstate._2 == state._2)
              equalKeyCardinality(state._2, nstate._2)
              assert(state._2.keys.length == nstate._2.keys.length)
      case Assign(to, _) =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              val toLoc = state._1.head(to)
              equalKeyCardPreserved(
                state._2 - toLoc, 
                nstate._2 - toLoc, 
                toLoc, 
                state._2(toLoc),
                nstate._2(toLoc))
              assert(nstate._2 - toLoc == state._2 - toLoc)
              equalKeyCardUpdateCommonKey(state._2, state._2, toLoc, v)
              assert(state._2.keys.length == nstate._2.keys.length)
            case Cmd(_, nstate) => 
              assert(nstate._2 == state._2)
              equalKeyCardinality(state._2, nstate._2)
              assert(state._2.keys.length == nstate._2.keys.length)
      case If(_, _) =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._2 == state._2)
              equalKeyCardinality(state._2, nstate._2)
              assert(state._2.keys.length == nstate._2.keys.length)
            case Cmd(_, nstate) => 
              assert(nstate._2 == state._2)
              equalKeyCardinality(state._2, nstate._2)
              assert(state._2.keys.length == nstate._2.keys.length)
      case While(_, _) =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._2 == state._2)
              equalKeyCardinality(state._2, nstate._2)
              assert(state._2.keys.length == nstate._2.keys.length)
            case Cmd(_, nstate) => 
              assert(nstate._2 == state._2)
              equalKeyCardinality(state._2, nstate._2)
              assert(state._2.keys.length == nstate._2.keys.length)
      case Seq(stmt1, _)   => 
        memIncreasesByOne(stmt1, state, v)
      case Block(stmt1)   => 
        memIncreasesByOne(stmt1, state, v)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match 
      case Left(_) => true
      case Right(conf) => conf match
        case St(nstate) => 
          nstate._2.keys.length == state._2.keys.length ||
          nstate._2.keys.length == state._2.keys.length + 1
        case Cmd(_, nstate) => 
          nstate._2.keys.length == state._2.keys.length ||
          nstate._2.keys.length == state._2.keys.length + 1
    )

  /*
  @extern @pure
  def uniqueLocsAxiom(state: State, name1: Name, name2: Name, loc: BigInt): Unit = {
    require(state._1.head(name1) == loc)
    require(name1 != name2)
  }.ensuring(state._1.head(name2) != loc)
  */

 /*
 def noDoubleLoc(loc: Loc, env: Env): Boolean = {
    env.values contains loc
 }


  // assume: locs in env < new loc
  // assume: no double locs in state
  def uniqueLocs(stmt: Stmt, state: State, name1: Name, name2: Name, loc: BigInt): BigInt = {
    val env = state._1
    val mem = state._2
    val loc = state._3
    require(env.head.isempty)
    loc
  }.ensuring(loc =>
    Interpreter.traceStmt1(stmt, state) match
      case Left(_)      => true
      case Right(conf)  => conf match
        case St(nstate)     => 
          nstate._1.values 
        case Cmd(_, nstate) => 
    )
  */

  def envListEquality(env1: EnvList, env2: EnvList, name: Name, l: Loc): Unit = {
    require(env1.head == env2.head)
    require(!(env1.head contains name))
    require(!(env2.head contains name))
  }.ensuring(env1.head == (env2.head + (name -> l)) - name)

  def envListPush(env: EnvList): EnvList = {
    env.push(env.head)
  }.ensuring(nenv => env.head == nenv.head)

  /*
  def envListPop(env: EnvList, name: Name): EnvList = {
    require(env.head contains name)
    env.tail
  }.ensuring(nenv => env.head(name) == nenv.head(name) || !(nenv.head contains name))
  */

  /*
  /* every env.head is a superset of env.tail.head */
  @extern @pure
  def prevEnvSubsetofHead(stmt: Stmt, state: State, name: Name): Unit = {
    require(state._1.head contains name)
    require(state._1.tail.head contains name)
    stmt match
      case Decl(nname, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
              /*
              envListEquality(state._1, state._1, nname, l)
              envListUpdated(state, nname)
              assert(nstate._1.head contains nname)
              assert(!(state._1.head contains nname))
              assert(nname != name)
              assert(nstate._1.head - nname == state._1.head)
              assert(nstate._1.head(name) == state._1.head(name))     // VALID, timeout: 60 secs
              */
            case Cmd(_, nstate)  =>
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
      case Assign(_, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
            case Cmd(_, nstate)  => 
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
      case If(_, _)       => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
            case Cmd(_, nstate)  =>
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
      case While(_, _)    =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) => 
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
            case Cmd(_, nstate)  => 
              assert(!(nstate._1.tail.head contains name) || (nstate._1.head contains name))
      case Seq(stmt1, _)  => 
        prevEnvSubsetofHead(stmt1, state, name)
      case Block(stmt1)   => 
        prevEnvSubsetofHead(stmt1, state, name)

  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_)      => true
      case Right(conf)  => conf match
        case St(nstate) =>
          !(nstate._1.tail.head contains name) ||
          (nstate._1.head contains name)
        case Cmd(_, nstate)  => 
          !(nstate._1.tail.head contains name) ||
          (nstate._1.head contains name)
    )
  */

 /*
  @extern @pure
  def locationDoesntChange(stmt: Stmt, state: State, name: Name, l: Loc): Unit = {
    decreases(stmt)
    require(state._1.head contains name)
    stmt match
      case Decl(nname, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              envListEquality(state._1, state._1, nname, l)
              envListUpdated(state, nname)
              assert(nstate._1.head contains nname)
              assert(!(state._1.head contains nname))
              assert(nname != name)
              assert(nstate._1.head - nname == state._1.head)
              assert(nstate._1.head(name) == state._1.head(name))     // VALID, timeout: 60 secs
            case Cmd(_, nstate)  =>
              assert(nstate._1 == state._1)
              assert(nstate._1.head(name) == state._1.head(name))     
      case Assign(_, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              assert(nstate._1 == state._1)
              assert(nstate._1.head(name) == state._1.head(name))
            case Cmd(_, nstate)  => 
              assert(nstate._1 == state._1)
              assert(nstate._1.head(name) == state._1.head(name))
      case If(_, _)       => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              //assert(nstate._1 == state._1)
              assert(nstate._1.head(name) == state._1.head(name))
            case Cmd(_, nstate)  =>
              //assert(nstate._1 == state._1)
              envListPush(state._1)
              assert(nstate._1.head(name) == state._1.head(name))   // Timeout
      case While(_, _)    =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) => 
              //assert(nstate._1 == state._1)
              assert(nstate._1.head(name) == state._1.head(name))
            case Cmd(_, nstate)  => 
              //assert(nstate._1 == state._1)
              envListPush(state._1)
              assert(nstate._1.head(name) == state._1.head(name))   // timeout
      case Seq(stmt1, _)  => 
        locationDoesntChange(stmt1, state, name, l)
      case Block(stmt1)   => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) => 
              assert(nstate._1.head(name) == state._1.head(name) || 
                !(nstate._1.head contains name))
            case Cmd(nstmt1, nstate)  => 
              locationDoesntChange(nstmt1, state, name, l)
             // assert(nstate._1.head(name) == state._1.head(name))   // timeout

  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_)      => true
      case Right(conf)  => conf match
        case St(nstate) =>
          nstate._1.head(name) == state._1.head(name) || 
          !(nstate._1.head contains name)
        case Cmd(_, nstate)  => 
          nstate._1.head(name) == state._1.head(name)
    )
  */

  /*
  def noNullPointers(stmt: Stmt, state: State, name: Name, l: Loc): Unit = {
    require(state._1.head contains name)
    require(state._2 contains state._1.head(name))
    stmt match
      case Decl(_, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              assert(nstate._2 contains state._1.head(name))
            case Cmd(_, nstate)  => 
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              //assert(nstate._2 contains nstate._1.head(name))
      case Assign(_, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              //assert(nstate._2 contains nstate._1.head(name))
            case Cmd(_, nstate)  => 
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              //assert(nstate._2 contains nstate._1.head(name))
      case If(_, _)       => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              assert(nstate._2 contains state._1.head(name))
              assert(nstate._2 contains nstate._1.head(name))
            case Cmd(_, nstate)  => 
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              assert(nstate._2 contains state._1.head(name))
              assert(nstate._2 contains nstate._1.head(name))
      case While(_, _)    =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              assert(nstate._2 contains state._1.head(name))
              assert(nstate._2 contains nstate._1.head(name))
            case Cmd(_, nstate)  => 
              locationDoesntChange(stmt, state, name, l)
              assert(nstate._1.head(name) == state._1.head(name))
              assert(nstate._2 contains state._1.head(name))
              assert(nstate._2 contains nstate._1.head(name))
      case Seq(stmt1, _)  => 
        locationDoesntChange(stmt, state, name, l)
        noNullPointers(stmt1, state, name, l)
      case Block(stmt1)   => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate)     => 
              locationDoesntChange(stmt, state, name, l)
              assert(!stmt1.isInstanceOf[Block])
              assert(!(nstate._1.head contains name) || (nstate._2 contains nstate._1.head(name)))
              //noNullPointers(stmt1, state, name, l)
            case Cmd(_, nstate) => 
              locationDoesntChange(stmt, state, name, l)
              assert(!stmt1.isInstanceOf[Block])
              assert(nstate._1.head(name) == state._1.head(name))
              assert(nstate._2 contains state._1.head(name))
              assert(nstate._2 contains nstate._1.head(name))
              //noNullPointers(stmt1, state, name, l)
  }.ensuring(
    Interpreter.traceStmt1(stmt, state) match
      case Left(_)      => true
      case Right(conf)  => conf match
        case St(nstate)     => 
          !(nstate._1.head contains name) || (nstate._2 contains nstate._1.head(name))
        case Cmd(_, nstate) => 
          nstate._2 contains nstate._1.head(name)
    )
  */

  def noNullPointers(stmt: Stmt, state: State, name: Name, v: Boolean): Unit = {
    require(!(state._2 contains state._3))
    require(!(state._2 contains state._3 + 1))
    require(!(state._2 contains state._3 + 2))
    stmt match
      case Decl(_, _)     =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              declUsesLoc(stmt, state)
              newLocNeverInMemory(stmt, state, v)
              locIncreasesByOne(stmt, state)
              assert(nstate._1.head(name) == state._3)
              assert(nstate._2 contains state._3)
              assert(nstate._2 contains nstate._1.head(name))
            case Cmd(_, nstate)  => 
              ()
      case Assign(_, _)   =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              ()
            case Cmd(_, nstate)  => 
              ()
      case If(_, _)       => 
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              ()
            case Cmd(_, nstate)  => 
              ()
      case While(_, _)    =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => ()
          case Right(conf)  => conf match
            case St(nstate) =>
              ()
            case Cmd(_, nstate)  => 
              ()
      case Seq(stmt1, _)  => 
        noNullPointers(stmt1, state, name, v)
      case Block(stmt1)   => 
        noNullPointers(stmt1, state, name, v)
  }.ensuring(
    stmt match
      case Decl(name, _) =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => true
          case Right(conf)  => conf match
            case St(nstate)     => 
              (nstate._2 contains nstate._1.head(name)) &&
              (nstate._1.head.keys.length == state._1.head.keys.length + 1)
            case Cmd(_, nstate) => 
              (nstate._2 contains nstate._1.head(name)) &&
              (nstate._1.head.keys.length == state._1.head.keys.length + 1)     // VALID
      case Block(_) => true
      case _ =>
        Interpreter.traceStmt1(stmt, state) match
          case Left(_)      => true
          case Right(conf)  => conf match
            case St(nstate)     => 
              nstate._1.head.keys.length == state._1.head.keys.length     // VALID
            case Cmd(_, nstate) => 
              nstate._1.head.keys.length == state._1.head.keys.length
    )

}
