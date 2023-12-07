structure Ident where
  name : String
deriving Repr

inductive Expr where
  | true
  | false
  | nand (left right : Expr)
  | ident : Ident → Expr
  | ref (of : Expr)
  | deref (of : Expr)
  -- TODO: introduce structs
  -- | struct (fields : List struct_field)
  -- | struct_field (name : String) (value: Expr)
  -- | field (of: Expr) (name: String)
deriving Repr

inductive Stmt where
  | decl (name : String) (value : Expr)
  | assign (to : Expr) (value : Expr)
  | if (condition : Expr) (body : Stmt)
  | while (condition : Expr) (body : Stmt)
  | block (statements : List Stmt)
  | swap (left right : Expr)
  | bye (ref : Ident)
deriving Repr
