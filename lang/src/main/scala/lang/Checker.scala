package lang

import Expr.*
import Stmt.*
import stainless.*
import stainless.collection.*
import stainless.lang.*

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
      case Free(name)        => (env.contains(name), env)
      case _Block(stmt0)     =>
        val (b, _) = stmtIsClosed(stmt0, env)
        (b, env)
    }

  def stmtHasNoRedeclarations(stmt: Stmt, env: Set[Name]): (Boolean, Set[Name]) =
    stmt match {
      case Decl(name, value) => (!env.contains(name), env + name)
      case Assign(to, value) => (true, env)
      case If(cond, body)    =>
        val (b, _) = stmtHasNoRedeclarations(body, env)
        (b, env)
      case Seq(stmt1, stmt2) =>
        val (s1, menv) = stmtHasNoRedeclarations(stmt1, env)
        val (s2, nenv) = stmtHasNoRedeclarations(stmt2, menv)
        (s1 && s2, nenv)
      case Free(name)        => (true, env)
      case _Block(stmt0)     =>
        val (b, _) = stmtHasNoRedeclarations(stmt0, env)
        (b, env)
    }

  def exprHasNoUseAfterFree(expr: Expr, freed: Set[Name]): Boolean = expr match {
    case True              => true
    case False             => true
    case Nand(left, right) =>
      exprHasNoUseAfterFree(left, freed) && exprHasNoUseAfterFree(right, freed)
    case Ident(name)       => !freed.contains(name)
  }

  def stmtHasNoUseAfterFree(
      stmt: Stmt,
      env: Set[Name],
      freed: Set[Name]
  ): (Boolean, Set[Name], Set[Name]) =
    stmt match {
      case Decl(name, value) => (exprHasNoUseAfterFree(value, freed), env + name, freed)
      case Assign(to, value) =>
        (!freed.contains(to) && exprHasNoUseAfterFree(value, freed), env, freed)
      case If(cond, body)    =>
        val (b, benv, bfreed) = stmtHasNoUseAfterFree(body, env, freed)
        (
          exprHasNoUseAfterFree(cond, freed) && b,
          env,
          // Conservatively assuming the If will always run. We ignore frees of
          // local variables as those are from a no longer existing scope.
          bfreed -- (benv -- env)
        )
      case Seq(stmt1, stmt2) =>
        val (s1, menv, mfreed) = stmtHasNoUseAfterFree(stmt1, env, freed)
        val (s2, nenv, nfreed) = stmtHasNoUseAfterFree(stmt2, menv, mfreed)
        (s1 && s2, nenv, nfreed)
      case Free(name)        => (!freed.contains(name), env, freed + name)
      case _Block(stmt0)     =>
        val (b, nenv, nfreed) = stmtHasNoUseAfterFree(stmt0, env, freed)
        (b, env, nfreed -- (nenv -- env))
    }

  // ---

  def stmtHasNoBlocks(stmt: Stmt): Boolean = stmt match
    case Decl(name, value) => true
    case Assign(to, value) => true
    case If(cond, body)    => stmtHasNoBlocks(body)
    case Seq(stmt1, stmt2) => stmtHasNoBlocks(stmt1) && stmtHasNoBlocks(stmt2)
    case Free(name)        => true
    case _Block(stmt0)     => false

}
