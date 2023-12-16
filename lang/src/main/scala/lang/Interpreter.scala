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
      state._1.get(name) match
        case Some(loc) =>
          state._2.get(loc) match
            case Some(value) => Right(value)
            case None()      => Left(Set(LangException.InvalidLoc))
        case None()    => Left(Set(LangException.UndeclaredVariable))


  def evalStmt1(stmt: Stmt, state: State): Either[Set[LangException], Conf] =
    val (env, mem, nl) = state
    stmt match
      case Decl(name, value)  => 
        (env.contains(name), evalExpr(value, state)) match
        case (false, Right(v)) =>
          Right(St(env + (name -> nl), mem + (nl -> v), nl + 1))
        case (false, Left(b))  => Left(b)
        case (true, Right(v))  => Left(Set(LangException.RedeclaredVariable)) 
        case (true, Left(b))   => Left(b + LangException.RedeclaredVariable)
      case Assign(to, value)  => 
        (env.get(to), evalExpr(value, state)) match
        case (Some(loc), Right(v)) => mem.contains(loc) match
          case true  => Right(St(env, mem.updated(loc, v), nl))
          case false => Left(Set(LangException.InvalidLoc))
        case (Some(loc), Left(b))  => mem.contains(loc) match
          case true  => Left(b)
          case false => Left(b + LangException.InvalidLoc)
        case (None(), Right(_))    => Left(Set(LangException.UndeclaredVariable)) 
        case (None(), Left(b))     => Left(b + LangException.UndeclaredVariable)
      case If(cond, body)    => evalExpr(cond, state) match
        case Left(b)  => Left(b)
        case Right(c) =>
          if c then Right(Cmd(body, state)) else Right(St(state))
      case Seq(stmt1, stmt2)  => evalStmt1(stmt1, state) match
        case Left(b)  => Left(b)
        case Right(c) => c match
          case St(nstate)          => Right(Cmd(stmt2, nstate))
          case Cmd(nstmt1, nstate) => Right(Cmd(Seq(nstmt1, stmt2), nstate))

  
  def evalStmt(stmt: Stmt, state: State): Either[Set[LangException], State] =
    evalStmt1(stmt, state) match
      case Left(b) => Left(b) 
      case Right(conf) => conf match
        case St(fstate) => Right(fstate)
        case Cmd(nstmt, nstate) => evalStmt(nstmt, nstate)
  
}
