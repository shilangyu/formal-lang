package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import stainless.annotation.{extern, pure}

import Expr.*
import Stmt.*
import Conf.*

object Interpreter {

  def evalExpr(expr: Expr, state: State): Either[Set[LangException], Boolean] =
    require(state._1.nonEmpty)
    expr match
      case True               => Right(true)
      case False              => Right(false)
      case Nand(left, right)  =>
        (evalExpr(left, state), evalExpr(right, state)) match
          case (Right(b1), Right(b2)) => Right(!(b1 && b2))
          case (Left(b1), Left(b2))   => Left(b1 ++ b2)
          case (Left(b1), _)          => Left(b1)
          case (_, Left(b2))          => Left(b2)
      case Ident(name)        =>
        state._1.head.get(name) match
          case Some(loc) =>
            state._2.get(loc) match
              case Some(value) => Right(value)
              case None()      => Left(Set(LangException.InvalidLoc))
          case None()    => Left(Set(LangException.UndeclaredVariable))


  def inclusion(env: Env, envs: List[Env]): Boolean = envs match
    case Cons(h, t) => keySet(h).subsetOf(keySet(env)) && inclusion(h, t) 
    case Nil() => true
  
  def consistency(stmt: Stmt, state: State, blocks: BigInt): Boolean =
    def rec(stmt: Stmt): (Boolean, BigInt) = {
      stmt match
        case Decl(name, value) => (true, BigInt(0))
        case Assign(to, value) => (true, BigInt(0))
        case If(cond, body) =>
          val (b, i) = rec(body)
          (b && i == 0, i)
        case Seq(stmt1, stmt2) =>
          val (b1, i1) = rec(stmt1)
          val (b2, i2) = rec(stmt2)
          (b1 && b2 && i2 == 0, i1)
        case _Block(stmt0) =>
          val (b, i) = rec(stmt0)
          (b, i + 1)
      }.ensuring(res => res._2 >= 0)
    val (b, i) = rec(stmt)
    blocks >= 0 && b && i + blocks + 1 == state._1.size && inclusion(state._1.head, state._1.tail)

  def consistency(state: State, blocks: BigInt): Boolean =
    blocks >= 0 && blocks + 1 == state._1.size && inclusion(state._1.head, state._1.tail)

  def evalStmt1(stmt: Stmt, state: State, blocks: BigInt): Either[Set[LangException], Conf] = {
    require(consistency(stmt, state, blocks))

    val (env, mem, nl) = state
    stmt match
      case Decl(name, value)  => (env.head.contains(name), evalExpr(value, state)) match
        case (false, Right(v)) =>
          subsetTest(env.head, name, nl)
          Right(St(env.head + (name -> nl) :: env.tail, mem + (nl -> v), nl + 1))
        case (false, Left(b))  => Left(b)
        case (true, Right(v))  => Left(Set(LangException.RedeclaredVariable)) 
        case (true, Left(b))   => Left(b + LangException.RedeclaredVariable)
      case Assign(to, value)  => (env.head.get(to), evalExpr(value, state)) match
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
          if c then Right(Cmd(_Block(body), (env.head :: env, mem, nl)))
          else Right(St(state))
      case Seq(stmt1, stmt2)  => evalStmt1(stmt1, state, blocks) match
        case Left(b)  => Left(b)
        case Right(conf) => conf match
          case St(nstate)          => Right(Cmd(stmt2, nstate))
          case Cmd(nstmt1, nstate) => Right(Cmd(Seq(nstmt1, stmt2), nstate))
      case _Block(stmt0)       => evalStmt1(stmt0, state, blocks + 1) match
        case Left(b)  => Left(b)
        case Right(conf) => conf match
          case St(nstate)         =>
            val (nenv, nmem, nnl) = nstate
            Right(St((nenv.tail, nmem, nnl)))
          case Cmd(nstmt0, nstate) => Right(Cmd(_Block(nstmt0), nstate))
  }.ensuring( res => res match
    case Left(b) => true 
    case Right(conf) => conf match
      case St(nstate) =>
        consistency(nstate, blocks)
      case Cmd(nstmt, nstate) =>
        consistency(nstmt, nstate, blocks)
  )
    
  def evalStmt(stmt: Stmt, state: State): Either[Set[LangException], State] =
    require(consistency(stmt, state, 0))
    evalStmt1(stmt, state, 0) match
      case Left(b) => Left(b) 
      case Right(conf) => conf match
        case St(fstate) => Right(fstate)
        case Cmd(nstmt, nstate) => evalStmt(nstmt, nstate)

  //def evalProg(prog: Stmt): Option[Set[LangException]] =
  //  require(consistency(prog, (List.empty, Map.empty, 1), 0))
  //  evalStmt(prog, (List.empty, Map.empty, 1)).left.toOption

}
