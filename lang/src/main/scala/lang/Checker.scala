package lang

import stainless.lang._
import stainless.collection._
import stainless.annotation._

import lang.{Name, Expr, Stmt}
import lang.{ExprVal, Env}
import lang.{Interpreter}

object Checker {

  // Check if there are access to undeclared variables
  def isExprClosed(expr: Expr, env: Env): Boolean = expr match {
    case Expr.True       => true
    case Expr.False      => true
    case Expr.Nand(l, r) => isExprClosed(l, env) && isExprClosed(r, env)
    case Expr.Ident(n)   => env.contains(n)
    //case Expr.Ref(e)     => isExprClosed(e, env)
    //case Expr.Deref(e)   => isExprClosed(e, env)
  } ensuring(_ => Interpreter.evalExpr(expr))

  // Check if there are access to undeclared variables
  def isClosed(prog: Stmt, envs: List[Env]): (Boolean, List[Env])= prog match {
    case Stmt.Decl(n, v)          => (true, envs.head.updated(n, 1)::envs.tail)
    case Stmt.Assign(n, v)        => (envs.head.contains(n), envs)
    case Stmt.If(cond, body)      => 
      val (b, envs1) = isClosed(body, envs) 
      (isExprClosed(cond, envs1.head) && b, envs1)
    case Stmt.While(cond, body)   => 
      val (b, envs1) = isClosed(body, envs)
      (isExprClosed(cond, envs1.head) && b, envs1)
    case Stmt.Seq(s1, s2)         => 
      val (b, envs1) = isClosed(s1, envs)
      if b then 
        val (b, envs2) = isClosed(s2, envs1) 
        (b, envs2)
      else (false, envs1)
    //case Stmt.Block(s)            => isClosed(s,envs.head::envs) 
    //case Stmt.Swap(e1, e2)        => isExprClosed(e1, envs.head) && isExprClosed(e2, envs.head)
    //case Stmt.Bye(n)              => envs.head.contains(n)
  }
}
