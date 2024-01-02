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

/-- Describes the result of evaluating a statement. Contains the resulting state as well as proofs for invariants. -/
structure EvalResult (stmt : Stmt) (env : Env) where
  newEnv : Env
  newMem : Memory
  -- proof that the env tracked by the type checker and the interpreter is the same
  sameEnv : typeCheckStmt stmt (keySet env) = some (keySet newEnv)


/-- Evaluates an expression given a proof that the type checker has accepted this input. -/
def evalExpr (expr : Expr) (env : Env) (mem : Memory) (h : typeCheckExpr expr (keySet env)) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.false
  | Expr.nand left right => !((evalExpr left env mem (typeCheckExpr_nandLeft h)) && (evalExpr right env mem (typeCheckExpr_nandRight h)))
  | Expr.ident name =>
    let loc := AList.get name env (typeCheckExpr_ident h)
    sorry -- TODO: retrieve from memory

def evalStmt (stmt : Stmt) (env : Env) (mem : Memory) (h : isTypeCheckedStmt stmt (keySet env)) : EvalResult stmt env := match stmt with
  | Stmt.decl name value =>
    let v := evalExpr value env mem (typeCheckStmt_declValue h)
    sorry -- TODO: store into memory
  | Stmt.assign target value =>
    let loc := AList.get target env (typeCheckStmt_targetExists h)
    sorry -- TODO: store into memory
  | Stmt.conditional condition body =>
    let cond := evalExpr condition env mem (typeCheckStmt_conditionalCond h)

    if cond then
      let res := evalStmt body env mem (typeCheckStmt_conditionalBody h)
      -- we drop the new env, but keep the new mem
      EvalResult.mk env res.newMem (by
        simp only [typeCheckStmt, typeCheckStmt_conditionalCond h, res.sameEnv, Option.isSome_some, Bool.and_self, ite_true]
      )
    else
      EvalResult.mk env mem (by
        simp only [typeCheckStmt, typeCheckStmt_conditionalCond h, Bool.true_and, ite_eq_left_iff, Bool.not_eq_true, Option.not_isSome, imp_false, Option.isNone_false_isSome]
        exact typeCheckStmt_conditionalBody h
      )
  | Stmt.seq left right =>
    let new := evalStmt left env mem (typeCheckStmt_seqLeft h)
    let newer := evalStmt right new.newEnv new.newMem (typeCheckStmt_seqRight h new.sameEnv)

    EvalResult.mk newer.newEnv newer.newMem (by
      simp only [typeCheckStmt, new.sameEnv, newer.sameEnv]
    )
