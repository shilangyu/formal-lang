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
  def isStmtClosed(stmt: Stmt, env: Env): Boolean = stmt match {
    case Decl(name, value)   => isExprClosed(value, env)
    case Assign(to, value)   => env.contains(to) && isExprClosed(value, env)
    case If(cond, body)      => isExprClosed(cond, env) && isStmtClosed(body, env)
    case While(cond, body)   => isExprClosed(cond, env) && isStmtClosed(body, env)
    case Seq(s1, s2)         =>
      isStmtClosed(s1, env) && (
        s1 match
          case Decl(name, _) => isStmtClosed(s2, env.updated(name, 0))
          case _ => isStmtClosed(s2, env)
      )
    //case Block(s)            => isClosed(s,envs.head::envs) 
    //case Swap(e1, e2)        => isExprClosed(e1, envs.head) && isExprClosed(e2, envs.head)
    //case Bye(n)              => envs.head.contains(n)
  }

  def isProgClosed(prog: Stmt): Boolean =
    isStmtClosed(prog, Map.empty[Name, Loc])
}
