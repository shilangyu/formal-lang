import Lang.Ast
import Mathlib.Data.List.AList
import Lang.Checker
import Lang.Helpers
import Lang.Allocator
import Mathlib.Data.Finset.Basic

/-!
# Interpreter

This module performs evaluation of the source code. It evaluates an AST given
a proof that the type checker has accepted this AST.
-/

/-- The environment maps variable names to memory locations. -/
abbrev Env := @AList Name (fun _ => Loc)

/-- A set of freed variables. -/
abbrev Freed := Finset Name

/-- Entries in env have allocated memory. -/
def hasValidLocs (env : Env) (mem : Memory) := ∀ name, ∀ loc, env.lookup name = some loc → loc ∈ mem

/-- Describes the result of evaluating a statement. Contains the resulting state as well as proofs for invariants. -/
structure EvalResult (stmt : Stmt) (env : Env) where
  newEnv : Env
  newMem : Memory
  -- proof that the env tracked by the type checker and the interpreter is the same
  sameEnv : typeCheckStmt stmt (keySet env) = some (keySet newEnv)
  -- proof that all items in env have entries in mem
  validLocs : hasValidLocs newEnv newMem

/-- Evaluates an expression given a proof that the type checker has accepted this input. -/
def evalExpr
  (expr : Expr) (env : Env) (mem : Memory)
  (h : typeCheckExpr expr (keySet env)) (validLocs : hasValidLocs env mem)
  : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.false
  | Expr.nand left right => !((evalExpr left env mem (typeCheckExpr_nandLeft h) validLocs) && (evalExpr right env mem (typeCheckExpr_nandRight h) validLocs))
  | Expr.ident name =>
    let loc := AList.get name env (typeCheckExpr_ident h)
    let val := AList.get loc mem (by
      have p : AList.lookup name env = some loc := by
        simp_all only [AList.get, Option.isSome_some]
        split
        simp_all only [Option.some.injEq, Option.isSome_some, heq_eq_eq]
      have q := validLocs name loc

      simp_all only [AList.get, Option.isSome_some, forall_true_left]
    )
    val

def evalStmt
  (stmt : Stmt) (env : Env) (mem : Memory)
  (h : isTypeCheckedStmt stmt (keySet env)) (validLocs : hasValidLocs env mem)
  : EvalResult stmt env := match stmt with
  | Stmt.decl name value =>
    let v := evalExpr value env mem (typeCheckStmt_declValue h) validLocs
    let al := alloc mem v
    let newEnv: Env := env.insert name al.1

    EvalResult.mk newEnv al.2 (by
      simp only [typeCheckStmt, typeCheckStmt_declValue h, typeCheckStmt_declNoRedecl h, Option.eqSome_else, Bool.true_and, ite_eq_left_iff, Bool.not_eq_true, Option.not_isSome, imp_false, Option.isNone_false_isSome, not_false_eq_true, ite_true, Option.some.injEq]
      exact AList.insert_set_preservation
    ) (by
      rw [hasValidLocs]
      intro name' loc' a
      simp only [alloc, AList.mem_insert]
      have tr := typeCheckStmt_declNoRedecl h
      -- TODO
      have as := validLocs name' loc'
      have t := validLocs name' loc' (by sorry)
      apply Or.inr t
    )
  | Stmt.assign target value =>
    let loc := AList.get target env (typeCheckStmt_targetExists h)
    let v := evalExpr value env mem (typeCheckStmt_assignValue h) validLocs
    let newMem: Memory := mem.insert loc v

    EvalResult.mk env newMem (by
      simp only [typeCheckStmt, typeCheckStmt_targetExists h, decide_True, typeCheckStmt_assignValue h, Bool.and_self, ite_true]
    ) (by
      rw [hasValidLocs]
      intro name loc' a
      simp only [AList.mem_insert]
      apply Or.inr
      apply validLocs
      exact a
    )
  | Stmt.conditional condition body =>
    let cond := evalExpr condition env mem (typeCheckStmt_conditionalCond h) validLocs

    if cond then
      let res := evalStmt body env mem (typeCheckStmt_conditionalBody h) validLocs
      -- we drop the new env, but keep the new mem
      EvalResult.mk env res.newMem (by
        simp only [typeCheckStmt, typeCheckStmt_conditionalCond h, res.sameEnv, Option.isSome_some, Bool.and_self, ite_true]
      ) (by
        rw [hasValidLocs]
        intros
        simp
        -- cases body
        -- TODO: prove by showing mem ⊆ res.newMem, then we imply from validLocs
        sorry
      )
    else
      EvalResult.mk env mem (by
        simp only [typeCheckStmt, typeCheckStmt_conditionalCond h, Bool.true_and, ite_eq_left_iff, Bool.not_eq_true, Option.not_isSome, imp_false, Option.isNone_false_isSome]
        exact typeCheckStmt_conditionalBody h
      ) validLocs
  | Stmt.while condition body => Id.run do
    let mut mem' := mem
    let mut h' := h
    let mut validLocs' := validLocs

    while evalExpr condition env mem (typeCheckStmt_whileCond h') validLocs do
      let res := evalStmt body env mem (typeCheckStmt_whileBody h') validLocs
      mem' := res.newMem
      -- validLocs' := res.validLocs

    EvalResult.mk env mem (by
      simp only [typeCheckStmt, typeCheckStmt_whileCond h, Bool.true_and, ite_eq_left_iff,
        Bool.not_eq_true, Option.not_isSome, imp_false, Option.isNone_false_isSome]
      exact typeCheckStmt_whileBody h
    ) validLocs
  | Stmt.seq left right =>
    let new := evalStmt left env mem (typeCheckStmt_seqLeft h) validLocs
    let newer := evalStmt right new.newEnv new.newMem (typeCheckStmt_seqRight h new.sameEnv) new.validLocs

    EvalResult.mk newer.newEnv newer.newMem (by
      simp only [typeCheckStmt, new.sameEnv, newer.sameEnv]
    ) newer.validLocs

def evalProgram (stmt : Stmt) (h : isTypeCheckedStmt stmt Finset.empty) : EvalResult stmt (List.toAList []) :=
  evalStmt stmt (List.toAList []) (List.toAList []) h (by
    simp only [AList.lookup_to_alist, List.dlookup_nil, IsEmpty.forall_iff, implies_true, hasValidLocs]
  )
