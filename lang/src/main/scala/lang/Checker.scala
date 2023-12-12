package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

import Expr.*
import Stmt.*

object Checker {

  // Check if there are access to undeclared variables
  def isExprClosed(expr: Expr, names: Set[Name]): Boolean = expr match {
    case True       => true
    case False      => true
    case Nand(left, right) => isExprClosed(left, names) && isExprClosed(right, names)
    case Ident(name)   => names.contains(name)
    //case Ref(e)     => isExprClosed(e, env)
    //case Deref(e)   => isExprClosed(e, env)
  }

  // Check if there are access to undeclared variables
  def isStmtClosed(stmt: Stmt, names: Set[Name]): (Boolean, Set[Name]) =
    stmt match {
    case Decl(name, value)   => (isExprClosed(value, names), names + name)
    case Assign(to, value)   => (names.contains(to) && isExprClosed(value, names), names)
    case If(cond, body)      =>
      val (c, _) = isStmtClosed(body, names)
      (isExprClosed(cond, names) && c, names)
    //case While(cond, body)   =>
    //  val (b, nenv) = isStmtClosed(body, env)
    //  (isExprClosed(cond, env) && b, nenv)
    case Seq(s1, s2)         =>
      val (c1, mnames) = isStmtClosed(s1, names)
      val (c2, fnames) = isStmtClosed(s2, mnames)
      (c1 && c2, fnames)
    //case Block(s)            => isClosed(s,envs.head::envs) 
    //case Swap(e1, e2)        => isExprClosed(e1, envs.head) && isExprClosed(e2, envs.head)
    //case Bye(n)              => envs.head.contains(n)
  }

  def isProgClosed(prog: Stmt): (Boolean, Set[Name]) =
    isStmtClosed(prog, Set.empty)
}
