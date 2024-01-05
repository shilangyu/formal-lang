package lang

import stainless.*
import stainless.collection.*
import stainless.lang.*

import Expr.*
import Stmt.*

object Checker {

  def exprIsClosed(expr: Expr, env: Set[Name]): Boolean = expr match {
    case True              => true
    case False             => true
    case Nand(left, right) =>
      exprIsClosed(left, env) && exprIsClosed(right, env)
    case Ident(name)       => env.contains(name)
  }

  def stmtIsClosed(stmt: Stmt, env: Set[Name]): (Boolean, Set[Name]) =
    stmt match {
      case Decl(name, value) => (exprIsClosed(value, env), env + name)
      case Assign(to, value) =>
        (env.contains(to) && exprIsClosed(value, env), env)
      case If(cond, body)    =>
        val (b, _) = stmtIsClosed(body, env)
        (exprIsClosed(cond, env) && b, env)
      case Seq(stmt1, stmt2) =>
        val (s1, menv) = stmtIsClosed(stmt1, env)
        val (s2, nenv) = stmtIsClosed(stmt2, menv)
        (s1 && s2, nenv)
      case _Block(stmt0)     =>
        val (b, _) = stmtIsClosed(stmt0, env)
        (b, env)
    }

  def progIsClosed(prog: Stmt): (Boolean, Set[Name]) =
    stmtIsClosed(prog, Set.empty)

  def stmtHasNoRedeclarations(stmt: Stmt, env: Set[Name]): Option[Set[Name]] =
    stmt match {
      case Decl(name, value) =>
        if env.contains(name) then None() else Some(env + name)
      case Assign(to, value) => Some(env)
      case If(cond, body)    => stmtHasNoRedeclarations(body, env)
      case Seq(stmt1, stmt2) =>
        stmtHasNoRedeclarations(stmt1, env) match
          case Some(nenv) => stmtHasNoRedeclarations(stmt2, nenv)
          case None()     => None()
      case _Block(stmt0)     => stmtHasNoRedeclarations(stmt0, env)
    }

  def progHasNoRedeclarations(prog: Stmt): Boolean =
    stmtHasNoRedeclarations(prog, Set.empty).isDefined

  // ---

  def stmtHasNoBlocks(stmt: Stmt): Boolean = stmt match
    case Decl(name, value) => true
    case Assign(to, value) => true
    case If(cond, body)    => stmtHasNoBlocks(body)
    case Seq(stmt1, stmt2) => stmtHasNoBlocks(stmt1) && stmtHasNoBlocks(stmt2)
    case _Block(stmt0)     => false

}
