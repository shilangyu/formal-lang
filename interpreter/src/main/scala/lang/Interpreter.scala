package lang

import stainless.*
import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

import Expr.*
import Stmt.*

object Interpreter {

  def evalExpr(expr: Expr, state: State): Either[Set[LangException], Boolean] = 
    expr match
      case True               => Right(true)
      case False              => Right(false)
      case Nand(left, right)  =>
        (evalExpr(left, state), evalExpr(right, state)) match
          case (Right(b1), Right(b2))       => Right(!(b1 && b2))
          case (Left(excep1), Left(excep2)) => Left(excep1 ++ excep2)
          case (Left(excep), _)             => Left(excep)
          case (_, Left(excep))             => Left(excep)
      case Ident(name)        =>
        state.env.get(name) match
          case Some(loc) =>
            state.mem.get(loc) match
              case Some(value) => Right(value)
              case None()      => Left(Set(LangException.InvalidLoc))
          case None()    => Left(Set(LangException.UndeclaredVariable))

  def evalStmt(stmt: Stmt, state: State): Either[Set[LangException], State] =
    stmt match
      case Decl(name, value)  =>
        (state.env.contains(name), evalExpr(value, state)) match
          case (false, Right(v))  =>
            val loc = state.nextLoc
            Right(State(state.env + (name -> loc), state.freed, state.mem + (loc -> v), loc + 1))
          case (false, Left(b))   => Left(b)
          case (true, Left(b))    => Left(b + LangException.RedeclaredVariable)
          case (true, _)          => Left(Set(LangException.RedeclaredVariable)) 
      case Assign(to, value)  =>
        (state.env.get(to), evalExpr(value, state)) match
          case (Some(loc), Right(v))  =>
            if state.mem.contains(loc) 
              then Right(State(state.env, state.freed, state.mem + (loc -> v), state.nextLoc))
              else Left(Set(LangException.InvalidLoc))
          case (Some(loc), Left(b))   =>
            if state.mem.contains(loc) then Left(b)
            else Left(b + LangException.InvalidLoc)
          case (None(), Left(b))      => Left(b + LangException.UndeclaredVariable)
          case (None(), _)            => Left(Set(LangException.UndeclaredVariable)) 
      case If(cond, body)     =>
        evalExpr(cond, state) match
          case Left(excep)  => Left(excep)
          case Right(value) =>
            if value then
              evalStmt(body, state) match
                case Left(excep) => Left(excep) 
                case _           => Right(state)
            else Right(state)
      //case w @ While(cond, body) =>
      //  evalExpr(cond, state) match
      //    case Left(b)  => Left(b) 
      //    case Right(c) =>
      //      if c then
      //        evalStmt(body, state) match
      //          case Left(b)  => Left(b) 
      //          case Right(s) => Right(s) // evalStmt(w, s)
      //      else Right(state)
      case Seq(stmt1, stmt2)        =>          
        evalStmt(stmt1, state) match
          case Left(excep)   => Left(excep) 
          case Right(mstate) => evalStmt(stmt2, mstate) match
            case Left(excep)   => Left(excep) 
            case Right(fstate) => Right(fstate)
      case Free(name)         =>
        state.env.get(name) match
          case Some(loc) =>
            state.mem.contains(loc) match
              case true  => Right(State(state.env, state.freed + name, state.mem - loc, state.nextLoc))
              case false => Left(Set(LangException.InvalidLoc))
          case None()    => Left(Set(LangException.UndeclaredVariable))
}
