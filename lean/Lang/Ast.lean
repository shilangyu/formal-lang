/-!
# AST

This module defines the abstract syntax tree of the language.
-/

/-- A newtype for a string representing an identifier. -/
structure Name where
  name : String
deriving Repr, DecidableEq

inductive Expr where
  | true
  | false
  | nand (left right : Expr)
  | ident (name : Name)
  -- | ref (of : Expr)
  -- | deref (of : Expr)
  -- TODO: introduce structs
  -- | struct (fields : List struct_field)
  -- | struct_field (name : String) (value: Expr)
  -- | field (of: Expr) (name: String)
deriving Repr

inductive Stmt where
  | decl (name : Name) (value : Expr)
  | assign (target : Name) (value : Expr)
  | conditional (condition : Expr) (body : Stmt)
  -- | while (condition : Expr) (body : Stmt)
  | seq (left right : Stmt)
  -- | swap (left right : Expr)
  -- | bye (ref : Name)
deriving Repr
