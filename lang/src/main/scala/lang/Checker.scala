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
  def isStmtClosed(stmt: Stmt, envs: List[Env]): (Boolean, List[Env]) = stmt match {
    case Decl(name, value)   => 
      val envs1 = envs.head.updated(name, 0)::envs.tail
      (isExprClosed(value, envs.head), envs1)
    case Assign(to, value)   => 
      (envs.head.contains(to) && isExprClosed(value, envs.head), envs)
    case If(cond, body)      =>
      val (b, envs1) = isStmtClosed(body, envs)
      (isExprClosed(cond, envs.head) && b, envs)
    //case While(cond, body)   =>
    //  val (b, nenv) = isStmtClosed(body, env)
    //  (isExprClosed(cond, env) && b, nenv)
    case Seq(stmt1, stmt2)         =>
      val (b1, envs1) = isStmtClosed(stmt1, envs)
      val (b2, envs2) = isStmtClosed(stmt2, envs1)
      (b1 && b2, envs2)
    case Block(_, stmt)            => 
      val (b, envs1) = isStmtClosed(stmt, envs.head::envs) 
      (b, envs1.tail)
    //case Swap(e1, e2)        => isExprClosed(e1, envs.head) && isExprClosed(e2, envs.head)
    //case Bye(n)              => envs.head.contains(n)
  }

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
