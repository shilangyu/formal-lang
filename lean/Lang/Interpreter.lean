import Lang.Ast
import Mathlib.Data.List.AList
import Lang.Checker
import Lang.Helpers

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
    evalStmt right newEnv newMem (by sorry)

lemma evalStmt_env_eq_typeCheck (h : isTypeCheckedStmt stmt (keySet env)) : typeCheckStmt stmt (keySet env) = some (keySet (evalStmt stmt env mem h).1) := by sorry
