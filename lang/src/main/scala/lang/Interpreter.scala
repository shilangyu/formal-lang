package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*

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
      (state._1.get(name): Option[Loc]) match
        case Some(loc) =>
          (state._2.get(loc): Option[Boolean]) match
            case Some(value) => Right(value)
            case None()        => Left(Set(LangException.InvalidLoc))
        case None()      => Left(Set(LangException.UndeclaredVariable))
    //case Expr.Ref(e)     => isExprClosed(e, env)
    //case Expr.Deref(e)   => isExprClosed(e, env)

  //def evalStmt(stmt: Stmt, state: State): Option[Set[LangException]] = stmt match
  //  case Decl(name, value) => 
  

}
