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
  def isStmtClosed(stmt: Stmt, env: Env): (Boolean, Env) = stmt match {
    case Decl(name, value)   => (isExprClosed(value, env), env + (name -> 0))
    case Assign(to, value)   => (env.contains(to) && isExprClosed(value, env), env)
    case If(cond, body)      =>
      val (c, _) = isStmtClosed(body, env)
      (isExprClosed(cond, env) && c, env)
    //case While(cond, body)   =>
    //  val (b, nenv) = isStmtClosed(body, env)
    //  (isExprClosed(cond, env) && b, nenv)
    case Seq(s1, s2)         =>
      val (c1, menv) = isStmtClosed(s1, env)
      val (c2, fenv) = isStmtClosed(s2, menv)
      (c1 && c2, fenv)
    //case Block(s)            => isClosed(s,envs.head::envs) 
    //case Swap(e1, e2)        => isExprClosed(e1, envs.head) && isExprClosed(e2, envs.head)
    //case Bye(n)              => envs.head.contains(n)
  }

  def isProgClosed(prog: Stmt): (Boolean, Env) =
    isStmtClosed(prog, Map.empty)
}
