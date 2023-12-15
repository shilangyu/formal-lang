import Lang.Ast
import Mathlib.Data.List.AList
import Mathlib.Data.Finset.Basic
import Lang.Checker

/-!
# Interpreter

This module performs evaluation of the source code. It evaluates an AST given
a proof that the type checker has accepted this AST.
-/

/-- A memory location represented as a natural number. -/
structure Loc where
  loc : Nat
deriving Repr, DecidableEq

/-- The environment maps variable names to memory locations. -/
abbrev Env := @AList Name (fun _ => Loc)
/-- The memory maps variable locations to values. -/
abbrev Memory := @AList Loc (fun _ => Bool)

/-- Returns a finite set of keys of an association list. -/
def keySet {α : Type} {β : α → Type} (a : @AList α β) : Finset α :=
  Finset.mk (Multiset.ofList a.keys) a.nodupKeys

/--
Establishes a correspondance between the finite set of variables in the type
checker and the association list in the interpreter.
-/
lemma identEnvVars (h : typeCheckExpr (Expr.ident name) (keySet env)) : (AList.lookup name env).isSome := by
  apply typeCheckExpr_ident at h
  exact AList.lookup_isSome.mpr h

/-- Evaluates an expression given a proof that the type checker has accepted this input. -/
def evalExpr (expr : Expr) (env : Env) (mem : Memory) (h : typeCheckExpr expr (keySet env)) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.false
  | Expr.nand left right => !((evalExpr left env mem (typeCheckExpr_nandLeft h)) && (evalExpr right env mem (typeCheckExpr_nandRight h)))
  | Expr.ident name => match AList.lookup name env, identEnvVars h with
    | some p, _ => sorry -- TODO: we need proofs about memory

-- def evalStmt (expr : Expr) (env : Env) (mem : Memory) (h : typeCheckExpr expr env) : Bool := match expr with
