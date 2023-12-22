package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*
import Conf.*

object Interpreter {

  def evalExpr(expr: Expr, state: State): Either[Set[LangException], Boolean] = expr match
    case True               => Right(true)
    case False              => Right(false)
    case Nand(left, right)  =>
      (evalExpr(left, state), evalExpr(right, state)) match
        case (Right(b1), Right(b2)) => Right(!(b1 && b2))
        case (Left(b1), Left(b2))   => Left(b1 ++ b2)
        case (Left(b1), _)          => Left(b1)
        case (_, Left(b2))          => Left(b2)
    case Ident(name)        =>
      val env = state._1.head
      env.get(name) match
        case Some(loc) =>
          state._2.get(loc) match
            case Some(value) => Right(value)
            case None()      => Left(Set(LangException.InvalidLoc))
        case None()      => Left(Set(LangException.UndeclaredVariable))
    //case Expr.Ref(e)     => isExprClosed(e, env)
    //case Expr.Deref(e)   => isExprClosed(e, env)
  
    /*

  def evalStmt(stmt: Stmt, state: State): Either[Set[LangException], State] = stmt match
    case Decl(name, value) =>
      (state._1.get(name), evalExpr(value, state)) match
        case (None(), Right(v)) =>
          val loc = state._3
          Right((state._1.updated(name, loc), state._2.updated(loc, v), loc + 1))
        case (None(), Left(b)) => Left(b)
        case (Some(_), Right(v)) => Left(Set(LangException.RedeclaredVariable)) 
        case (Some(_), Left(b)) => Left(b + LangException.RedeclaredVariable)
    case Assign(to, value) =>
      (state._1.get(to), evalExpr(value, state)) match
        case (Some(loc), Right(v)) =>
          state._2.get(loc) match
            case Some(_) => Right((state._1, state._2.updated(loc, v), state._3))
            case None()  => Left(Set(LangException.InvalidLoc))
        case (Some(loc), Left(b)) =>
          state._2.get(loc) match
            case Some(_) => Left(b)
            case None()  => Left(b + LangException.InvalidLoc)
        case (None(), Right(_)) => Left(Set(LangException.UndeclaredVariable)) 
        case (None(), Left(b)) => Left(b + LangException.UndeclaredVariable)
    case If(cond, body) =>
      evalExpr(cond, state) match
        case Left(b) => Left(b) 
        case Right(c) =>
          if c then
            evalStmt(body, state) match
              case Left(b2) => Left(b2) 
              case Right(_) => Right(state)     // fix this
          else Right(state)
    //case w @ While(cond, body) =>
    //  evalExpr(cond, state) match
    //    case Left(b) => Left(b) 
    //    case Right(c) =>
    //      if c then
    //        evalStmt(body, state) match
    //          case Left(b) => Left(b) 
    //          case Right(s) => Right(s) // evalStmt(w, s)
    //      else Right(state)
    case Seq(s1, s2) =>          
      evalStmt(s1, state) match
        case Left(b) => Left(b) 
        case Right(s) => evalStmt(s2, s)

        */

  /*
  def getTopEnv(state: State): Either[Set[LangException], Env] = 
    val envs = state._1
    envs match
      case Nil() => Left(Set(LangException.EmptyEnvs))
      case Cons(env, _) => Right(env)

  def getEnvTail(state: State): Either[Set[LangException], List[Env]] = 
    val envs = state._1
    envs match
      case Nil() => Left(Set(LangException.EmptyEnvs))
      case Cons(_, Nil()) => Left(Set(LangException.EmptyEnvs))
      case Cons(_, envs) => Right(envs)

  def twoEnvs(conf: Conf): Boolean = conf match
    case St(state) => state._1.length > 2
    case Cmd(_, state) => state._1.length > 2
    */

  def traceStmt1(stmt: Stmt, state: State): Either[Set[LangException], Conf] =
    //decreases(conf)
      val (env, mem, loc) = state
      stmt match
        case Decl(name, value)    => 
          (env.head.get(name), evalExpr(value, state)) match
          case (None(), Right(v))   =>
            Right(St(env.tail.push(env.head + (name -> loc)), mem + (loc -> v), loc + 1))
          case (None(), Left(b))    => Left(b)
          case (Some(_), Right(v))  => Left(Set(LangException.RedeclaredVariable)) 
          case (Some(_), Left(b))   => Left(b + LangException.RedeclaredVariable)
        case Assign(to, value)    => 
          (env.head.get(to), evalExpr(value, state)) match
          case (Some(l), Right(v))  => mem.get(l) match
            case Some(_) => Right(St(env, mem.updated(l, v), loc))
            case None()  => Left(Set(LangException.InvalidLoc))
          case (Some(loc), Left(b))   => mem.get(loc) match
            case Some(_) => Left(b)
            case None()  => Left(b + LangException.InvalidLoc)
          case (None(), Right(_))     => Left(Set(LangException.UndeclaredVariable)) 
          case (None(), Left(b))      => Left(b + LangException.UndeclaredVariable)
        case If(cond, body)       => evalExpr(cond, state) match
          case Left(b)  => Left(b) 
          case Right(c) =>
            if c then 
              val statePush = (env.push(env.head), mem, loc)
              Right(Cmd(Block(body), statePush))
            else Right(St(state))
        case While(cond, body)    => evalExpr(cond, state) match
          case Left(b)  => Left(b) 
          case Right(c) =>
            if c then 
              val statePush = (env.push(env.head), mem, loc)
              Right(Cmd(Seq(Block(body), stmt), statePush))
            else Right(St(state))
        case Seq(stmt1, stmt2)          => traceStmt1(stmt1, state) match
          case Left(b)  => Left(b)
          case Right(c) => c match
            case St(nstate)         => Right(Cmd(stmt2, nstate))
            case Cmd(nstmt1, nstate) => Right(Cmd(Seq(nstmt1, stmt2), nstate)) 
        case Block(stmt1)          => traceStmt1(stmt1, state) match
          case Left(b)  => Left(b)
          case Right(c) => c match
            case St(nstate)         => 
              val (nenv, nmem, nloc) = nstate
              val nstatepop = (nenv.tail, nmem, nloc)
              Right(St(nstatepop))
            case Cmd(nstmt1, nstate) => Right(Cmd(Block(nstmt1), nstate)) 
            /*
        case Block(true, stmt1)          => 
          val statePush = (env.push(env.head), mem, nl)     // entering the block
          traceStmt1(stmt1, statePush) match
          case Left(b)  => Left(b)
          case Right(c) => c match
            case St(state1)         => 
              val (env1, mem1, nl1) = state1
              val state1pop = (env1.tail, mem1, nl1)
              Right(St(state1pop))
            case Cmd(stmt1, state1) => Right(Cmd(Block(false, stmt1), state1)) 
        case Block(false, stmt1)          => traceStmt1(stmt1, state) match
          case Left(b)  => Left(b)
          case Right(c) => c match
            case St(state1)         => 
              val (env1, mem1, nl1) = state1
              val state1pop = (env1.tail, mem1, nl1)
              Right(St(state1pop))
            case Cmd(stmt2, state1) => Right(Cmd(Block(false, stmt2), state1)) 
            */

}
