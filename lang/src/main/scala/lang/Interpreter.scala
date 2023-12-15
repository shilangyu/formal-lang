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


  def traceStmt1(conf: Conf): Either[Set[LangException], Conf] =
    decreases(conf)
    //require(twoEnvs(conf))
    conf match
      case St(state)  =>
        Right(St(state))
      case Cmd(stmt, state) => 
        val envsTail = state._1.tail
        val env = state._1.head
        stmt match
          case Decl(name, value)    => 
            (env.get(name), evalExpr(value, state)) match
            case (None(), Right(v))   =>
              val loc = state._3
              val env1 = env.updated(name,loc)
              Right(St(env1::envsTail, state._2.updated(loc, v), loc + 1))
            case (None(), Left(b))    => Left(b)
            case (Some(_), Right(v))  => Left(Set(LangException.RedeclaredVariable)) 
            case (Some(_), Left(b))   => Left(b + LangException.RedeclaredVariable)
          case Assign(to, value)    => 
            (env.get(to), evalExpr(value, state)) match
            case (Some(loc), Right(v))  => state._2.get(loc) match
              case Some(_) => Right(St(state._1, state._2.updated(loc, v), state._3))
              case None()  => Left(Set(LangException.InvalidLoc))
            case (Some(loc), Left(b))   => state._2.get(loc) match
              case Some(_) => Left(b)
              case None()  => Left(b + LangException.InvalidLoc)
            case (None(), Right(_))     => Left(Set(LangException.UndeclaredVariable)) 
            case (None(), Left(b))      => Left(b + LangException.UndeclaredVariable)
          case If(cond, body)       => evalExpr(cond, state) match
            case Left(b)  => Left(b) 
            case Right(c) =>
              if c then Right(Cmd(body, state))
              else Right(St(state))
          case Seq(stmt1, stmt2)          => traceStmt1(Cmd(stmt1, state)) match
            case Left(b)  => Left(b)
            case Right(c) => c match
              case St(state1)         => Right(Cmd(stmt2, state1))
              case Cmd(stmt1, state1) => Right(Cmd(Seq(stmt1, stmt2), state1)) 
          case Block(true, stmt)          => 
            val statePush = (env::envsTail, state._2, state._3)     // entering the block
            traceStmt1(Cmd(stmt, statePush)) match
            case Left(b)  => Left(b)
            case Right(c) => c match
              case St(state1)         => 
                val state1pop = (state1._1.tail, state1._2, state1._3)
                Right(St(state1pop))
              case Cmd(stmt1, state1) => Right(Cmd(Block(false, stmt1), state1)) 
          case Block(false, stmt)          => traceStmt1(Cmd(stmt, state)) match
            case Left(b)  => Left(b)
            case Right(c) => c match
              case St(state1)         => 
                val state1pop = (state1._1.tail, state1._2, state1._3)
                Right(St(state1pop))
              case Cmd(stmt1, state1) => Right(Cmd(Block(false, stmt1), state1)) 

}
