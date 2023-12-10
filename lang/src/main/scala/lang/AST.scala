package lang

type Name = String

enum Expr {
  case True
  case False
  case Nand(val left: Expr, val right: Expr)

  case Ident(val name: Name)

  //case Ref(val of: Expr)
  //case Deref(val of: Expr)

  // TODO: introduce structs
  // case Struct(val fields: List[StructField])
  // case StructField(val name: Name, val value: Expr)
  // case Field(val of: Expr, val name: Name)
}

enum Stmt {
  case Decl(val name: Name, val value: Expr)
  case Assign(val to: Name, val value: Expr)
  case If(val condition: Expr, val body: Stmt)
  case While(val condition: Expr, val body: Stmt)
  case Seq(val s1: Stmt, val s2: Stmt)
  //case Block(val stmt: Stmt)
  //case Swap(val left: Expr, val right: Expr)
  //case Bye(val ref: Name)
}
