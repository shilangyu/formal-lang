package lang

class Ident(val name: String) 

enum Expr {
  case True
  case False
  case Nand(val left: Expr, val right: Expr)

  case Var(val of: Ident)

  case Ref(val of: Ident)     // -> Loc
  case Deref(val of: Ident)   // -> <T>

  // TODO: introduce structs
  // case Struct(val fields: List[StructField])
  // case StructField(val name: String, val value: Expr)
  // case Field(val of: Expr, val name: String)
}

enum Stmt {
  // define a memory location
  case Decl(val name: Ident)                        
  // store a value in the memory location binded to an ident
  case Assign(val to: Ident, val value: Expr)       
  // store a value in a new memory location then 
  // store the reference in the memory location binded to an ident
  // x := ref True
  case RefAssign(val to: Ident, val value: Expr)    
  // store a value to the memory location represented by the value in the location binded to ident
  // !x := True
  case DerefAssign(val to: Ident, val value: Expr)  

  case If(val condition: Expr, val then: Stmt, val else: Stmt)
  case While(val condition: Expr, val body: Stmt)

  case Block(val statments: List[Stmt])

  case Swap(val left: Expr, val right: Expr)

  case Bye(val ref: Ident)
}
