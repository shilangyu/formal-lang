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

instance [Repr α] [∀ a, Repr (β a)] : ToString (@AList α β) where
  toString l := "{" ++ (l.entries |> List.map (fun e => s!"{reprStr e.fst}: {reprStr e.snd}") |> String.intercalate ", ") ++ "}"

/-- Returns a finite set of keys of an association list. -/
def keySet {α : Type} {β : α → Type} (a : @AList α β) : Finset α :=
  Finset.mk (Multiset.ofList a.keys) a.nodupKeys

/-- Given a proof that key ∈ assocList, lookups the key without fail. -/
def AList.get [DecidableEq α] (key : α) (assocList : AList β) (h : key ∈ assocList) : β key :=
  have isSome : (assocList.lookup key).isSome := by exact AList.lookup_isSome.mpr h

  match assocList.lookup key, isSome with
    | some v, _ => v

/-- Evaluates an expression given a proof that the type checker has accepted this input. -/
def evalExpr (expr : Expr) (env : Env) (mem : Memory) (h : typeCheckExpr expr (keySet env)) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.false
  | Expr.nand left right => !((evalExpr left env mem (typeCheckExpr_nandLeft h)) && (evalExpr right env mem (typeCheckExpr_nandRight h)))
  | Expr.ident name =>
    let loc := AList.get name env (typeCheckExpr_ident h)
    sorry -- TODO: retrieve from memory

def evalStmt (stmt : Stmt) (env : Env) (mem : Memory) (h : isTypeCheckedStmt stmt (keySet env)) : Env × Memory := match stmt with
  | Stmt.decl name value =>
    let v := evalExpr value env mem (typeCheckStmt_declValue h)
    sorry -- TODO: store into memory
  | Stmt.assign target value =>
    let loc := AList.get target env (typeCheckStmt_targetExists h)
    sorry -- TODO: store into memory
  | Stmt.conditional condition body =>
    let cond := evalExpr condition env mem (typeCheckStmt_conditionalCond h)
    let (newEnv, newMem) := if cond then evalStmt body env mem (typeCheckStmt_conditionalBody h) else (env, mem)

    -- we drop the new env, but keep the new mem
    (env, newMem)
  | Stmt.seq left right =>
    let (newEnv, newMem) := evalStmt left env mem (typeCheckStmt_seqLeft h)
    sorry
