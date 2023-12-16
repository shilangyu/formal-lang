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
    //case Ref(e)     => isExprClosed(e, env)
    //case Deref(e)   => isExprClosed(e, env)
  }

  // Check if there are access to undeclared variables
  def isStmtClosed(stmt: Stmt, env: EnvList): (Boolean, EnvList) = 
    stmt match
      case Decl(name, value)    => 
        val env1 = env.tail.push((env.head + (name -> 0)))
        (isExprClosed(value, env1.head), env1)
      case Assign(to, value)    => 
        (env.head.contains(to) && isExprClosed(value, env.head), env)
      case If(cond, body)       =>
        val (b, _) = isStmtClosed(body, env)
        (isExprClosed(cond, env.head) && b, env)
      //case While(cond, body)   =>
      //  val (b, nenv) = isStmtClosed(body, env)
      //  (isExprClosed(cond, env) && b, nenv)
      case Seq(stmt1, stmt2)    =>
        val (b1, env1) = isStmtClosed(stmt1, env)
        val (b2, env2) = isStmtClosed(stmt2, env1)
        (b1 && b2, env2)
      case Block(true, stmt)    => 
        val (b, _) = isStmtClosed(stmt, env) 
        (b, env)
      case Block(false, stmt)   => 
        val (b, env1) = isStmtClosed(stmt, env) 
        (b, env1)

  /*
  def isProgClosed(prog: Stmt): (Boolean, Env) =
    isStmtClosed(prog, Map.empty[Name, Loc])

  def noRedecl(stmt: Stmt, env: Env): (Boolean, Env) = stmt match {
    case Decl(name, value)   => (!env.contains(name), env.updated(name, 0))
    case Assign(to, value)   => (true, env)
    case If(cond, body)      => 
      val (b, env1) =  noRedecl(body, env)
      (b, env)
    //case While(cond, body)   =>
    //  val (b, nenv) = isStmtClosed(body, env)
    //  (isExprClosed(cond, env) && b, nenv)
    case Seq(s1, s2)         =>
      val (b1, env1) = noRedecl(s1, env)
      val (b2, env2) = noRedecl(s2, env1)
      (b1 && b2, env2)
    //case Block(s)            => isClosed(s,envs.head::envs) 
    //case Swap(e1, e2)        => isExprClosed(e1, envs.head) && isExprClosed(e2, envs.head)
    //case Bye(n)              => envs.head.contains(n)
  }
  */

}
