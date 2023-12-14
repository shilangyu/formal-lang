package lang

import stainless.*
import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

import Expr.*
import Stmt.*

object Interpreter {

  def evalExpr(expr: Expr, state: State): Either[Set[LangException], Boolean] = expr match
    case True               => Right(true)
    case False              => Right(false)
    case Nand(left, right)  =>
      (evalExpr(left, state), evalExpr(right, state)) match
        case (Right(b1), Right(b2))       => Right(!(b1 && b2))
        case (Left(excep1), Left(excep2)) => Left(excep1 ++ excep2)
        case (Left(excep), _)             => Left(excep)
        case (_, Left(excep))             => Left(excep)
    case Ident(name)        =>
      state._1.get(name) match
        case Some(loc) =>
          state._2.get(loc) match
            case Some(value) => Right(value)
            case None()      => Left(Set(LangException.InvalidLoc))
        case None()    => Left(Set(LangException.UndeclaredVariable))
    //case Expr.Ref(e)       => isExprClosed(e, env)
    //case Expr.Deref(e)     => isExprClosed(e, env)

  def evalStmt(stmt: Stmt, state: State): Either[Set[LangException], State] =
    stmt match
    case Decl(name, value)  =>
      (state._1.contains(name), evalExpr(value, state)) match
        case (false, Right(v))  =>
          val loc = state._3
          Right((state._1 + (name -> loc), state._2.updated(loc, v), loc + 1))
        case (false, Left(b))   => Left(b)
        case (true, Left(b))    => Left(b + LangException.RedeclaredVariable)
        case (true, _)          => Left(Set(LangException.RedeclaredVariable)) 
    case Assign(to, value)  =>
      (state._1.get(to), evalExpr(value, state)) match
        case (Some(loc), Right(v))  =>
          if state._2.contains(loc) then Right((state._1, state._2.updated(loc, v), state._3))
          else Left(Set(LangException.InvalidLoc))
        case (Some(loc), Left(b))   =>
          if state._2.contains(loc) then Left(b)
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
    case Seq(s1, s2)        =>          
      evalStmt(s1, state) match
        case Left(excep)   => Left(excep) 
        case Right(mstate) => evalStmt(s2, mstate) match
          case Left(excep)   => Left(excep) 
          case Right(fstate) => Right(fstate)
}
