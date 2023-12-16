package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*

object Checker {

  // Check if there are access to undeclared variables
  def isExprClosed(expr: Expr, env: Env): Boolean = expr match {
    case True       => true
    case False      => true
    case Nand(left, right) => isExprClosed(left, env) && isExprClosed(right, env)
    case Ident(name)   => env.contains(name)
  }

  // Check if there are access to undeclared variables
  def isStmtClosed(stmt: Stmt, env: EnvList): (Boolean, EnvList) = 
    stmt match
      case Decl(name, value)    => 
        val env1 = env.tail.push((env.head + (name -> 0)))
        (isExprClosed(value, env.head), env1)
      case Assign(to, value)    => 
        (env.head.contains(to) && isExprClosed(value, env.head), env)
      case If(cond, body)       =>
        val (b, _) = isStmtClosed(body, env)
        (isExprClosed(cond, env.head) && b, env)
      case While(cond, body)   =>
        val (b, _) = isStmtClosed(body, env)
        (isExprClosed(cond, env.head) && b, env)
      case Seq(stmt1, stmt2)    =>
        val (b1, env1) = isStmtClosed(stmt1, env)
        val (b2, env2) = isStmtClosed(stmt2, env1)
        (b1 && b2, env2)
      case Block(true, stmt1)    => 
        val (b, _) = isStmtClosed(stmt1, env.push(env.head)) 
        (b, env)
      case Block(false, stmt1)   => 
        val (b, _) = isStmtClosed(stmt1, env) 
        (b, env)

        /*
  def isProgClosed(prog: Stmt): (Boolean, EnvList) =
    isStmtClosed(prog, Map.empty[Name, Loc].asInstanceOf[Env])
  */

  def noRedecl(stmt: Stmt, env: EnvList): (Boolean, EnvList) = stmt match {
    case Decl(name, value)    => 
      (!env.head.contains(name), env.tail.push(env.head + (name -> 0)))
    case Assign(to, value)    => (true, env)
    case If(cond, body)       => 
      val (b, _) =  noRedecl(body, env)
      (b, env)
    case While(cond, body)    => 
      val (b, _) =  noRedecl(body, env)
      (b, env)
    case Seq(stmt1, stmt2)    =>
      val (b1, env1) = noRedecl(stmt1, env)
      val (b2, env2) = noRedecl(stmt2, env1)
      (b1 && b2, env2)
    case Block(true, stmt1)   => 
      val (b, _) = noRedecl(stmt1, env.push(env.head))
      (b, env)
    case Block(false, stmt1)  => 
      val (b, _) = noRedecl(stmt1, env) 
      (b, env)
  }

}
