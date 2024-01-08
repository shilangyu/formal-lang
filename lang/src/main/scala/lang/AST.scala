package lang

import stainless.*
import stainless.collection.*
import stainless.lang.*

type Name = String

enum Expr {
  case True
  case False
  case Nand(val left: Expr, val right: Expr)

  case Ident(val name: Name)
}

enum Stmt {
  case Decl(val name: Name, val value: Expr)
  case Assign(val to: Name, val value: Expr)

  case If(val cond: Expr, val body: Stmt)
  case Seq(val stmt1: Stmt, val stmt2: Stmt)

  case Free(val name: Name)

  case _Block(val stmt: Stmt)
}
