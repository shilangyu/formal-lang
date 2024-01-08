package lang

import stainless.*
import stainless.annotation.extern
import stainless.annotation.pure
import stainless.collection.*
import stainless.lang.*

import Expr.*
import Stmt.*
import Conf.*

object Interpreter {

  def evalExpr(expr: Expr, state: State): Either[Set[LangException], Boolean] =
    expr match
      case True              => Right(true)
      case False             => Right(false)
      case Nand(left, right) =>
        (evalExpr(left, state), evalExpr(right, state)) match
          case (Right(b1), Right(b2)) => Right(!(b1 && b2))
          case (Left(b1), Left(b2))   => Left(b1 ++ b2)
          case (Left(b1), _)          => Left(b1)
          case (_, Left(b2))          => Left(b2)
      case Ident(name)       =>
        if state.envs.isEmpty then Left(Set(LangException._EmptyEnvStack))
        else
          state.envs.head.get(name) match
            case Some(loc) =>
              state.mem.get(loc) match
                case Some(value) => Right(value)
                case None()      => Left(Set(LangException.InvalidLoc))
            case None()    => Left(Set(LangException.UndeclaredVariable))

  def evalStmt1(stmt: Stmt, state: State, blocks: BigInt): Either[Set[LangException], Conf] = {
    val State(envs, mem, nl) = state
    stmt match
      case Decl(name, value) =>
        if envs.isEmpty then Left(Set(LangException._EmptyEnvStack))
        else
          (envs.head.contains(name), evalExpr(value, state)) match
            case (false, Right(v)) =>
              Right(
                St(
                  State(
                    envs.head + (name -> nl) :: envs.tail,
                    mem + (nl         -> v),
                    nl + 1
                  )
                )
              )
            case (false, Left(b))  => Left(b)
            case (true, Right(v))  => Left(Set(LangException.RedeclaredVariable))
            case (true, Left(b))   => Left(b + LangException.RedeclaredVariable)
      case Assign(to, value) =>
        if envs.isEmpty then Left(Set(LangException._EmptyEnvStack))
        else
          (envs.head.get(to), evalExpr(value, state)) match
            case (Some(loc), Right(v)) =>
              mem.contains(loc) match
                case true  => Right(St(State(envs, mem.updated(loc, v), nl)))
                case false => Left(Set(LangException.InvalidLoc))
            case (Some(loc), Left(b))  =>
              mem.contains(loc) match
                case true  => Left(b)
                case false => Left(b + LangException.InvalidLoc)
            case (None(), Right(_))    => Left(Set(LangException.UndeclaredVariable))
            case (None(), Left(b))     => Left(b + LangException.UndeclaredVariable)
      case If(cond, body)    =>
        evalExpr(cond, state) match
          case Left(b)  => Left(b)
          case Right(c) =>
            if c then
              if envs.isEmpty then Left(Set(LangException._EmptyEnvStack))
              else Right(Cmd(_Block(body), State(envs.head :: envs, mem, nl)))
            else Right(St(state))
      case Seq(stmt1, stmt2) =>
        evalStmt1(stmt1, state, blocks) match
          case Left(b)     => Left(b)
          case Right(conf) =>
            conf match
              case St(nstate)          => Right(Cmd(stmt2, nstate))
              case Cmd(nstmt1, nstate) => Right(Cmd(Seq(nstmt1, stmt2), nstate))
      case Free(name)        =>
        if envs.isEmpty then Left(Set(LangException._EmptyEnvStack))
        else
          envs.head.get(name) match
            case Some(loc) =>
              mem.contains(loc) match
                case true  => Right(St(State(envs, mem.removed(loc), nl)))
                case false => Left(Set(LangException.InvalidLoc))
            case None()    => Left(Set(LangException.UndeclaredVariable))
      case _Block(stmt0)     =>
        evalStmt1(stmt0, state, blocks + 1) match
          case Left(b)     => Left(b)
          case Right(conf) =>
            conf match
              case St(nstate)          =>
                val State(nenv, nmem, nnl) = nstate
                if nenv.isEmpty then Left(Set(LangException._EmptyEnvStack))
                else Right(St(State(nenv.tail, nmem, nnl)))
              case Cmd(nstmt0, nstate) => Right(Cmd(_Block(nstmt0), nstate))
  }

  def evalStmt(stmt: Stmt, state: State): Either[Set[LangException], State] =
    evalStmt1(stmt, state, 0) match
      case Left(b)     => Left(b)
      case Right(conf) =>
        conf match
          case St(fstate)         => Right(fstate)
          case Cmd(nstmt, nstate) => evalStmt(nstmt, nstate)
}
