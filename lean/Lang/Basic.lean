import Lang.Ast
import Mathlib.Data.List.AList
import Mathlib.Data.Finset.Basic

structure Loc where
  loc : Nat
deriving Repr, DecidableEq

inductive Result {α β : Type} where
  | ok (value : α)
  | err (error : β)
deriving Repr

abbrev Env := @AList Name (fun _ => Loc)
abbrev Memory := @AList Loc (fun _ => Bool)

def typeCheckExpr (expr : Expr) (env : Env) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.true
  | Expr.nand left right => (typeCheckExpr left env) && (typeCheckExpr right env)
  | Expr.ident name => (AList.lookup name env).isSome
  -- | Expr.ref of => Bool.true
  -- | Expr.deref of => Bool.true

theorem typeCheckExpr_nandLeft (h : typeCheckExpr (Expr.nand left right) env) : typeCheckExpr left env := by
  unfold typeCheckExpr at h
  simp [Bool.coe_and_iff] at h
  apply And.left at h
  exact h

theorem typeCheckExpr_nandRight (h : typeCheckExpr (Expr.nand left right) env) : typeCheckExpr right env := by
  unfold typeCheckExpr at h
  simp [Bool.coe_and_iff] at h
  apply And.right at h
  exact h

theorem typeCheckExpr_ident (h : typeCheckExpr (Expr.ident name) env) : (AList.lookup name env).isSome := by
  unfold typeCheckExpr at h
  exact h

def evalExpr (expr : Expr) (env : Env) (mem : Memory) (h : typeCheckExpr expr env) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.false
  | Expr.nand left right => !((evalExpr left env mem (typeCheckExpr_nandLeft h)) && (evalExpr right env mem (typeCheckExpr_nandRight h)))
  | Expr.ident name => match AList.lookup name env, typeCheckExpr_ident h with
    | some p, _ => true -- TODO: we need proofs about memory

-- def evalStmt (expr : Expr) (env : Env) (mem : Memory) (h : typeCheckExpr expr env) : Bool := match expr with


def typeCheckStmt (stmt : Stmt) (env : Env) : Bool := match stmt with
  | Stmt.decl name value =>  (AList.lookup name env).isNone && (typeCheckExpr value env)
  | Stmt.assign target value => (AList.lookup target env).isSome && (typeCheckExpr value env)
  | Stmt.conditional condition body => (typeCheckExpr condition env) && (typeCheckStmt body env)

def isClosedExpr (expr : Expr) (env : Env) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.true
  | Expr.nand left right => (isClosedExpr left env) && (isClosedExpr right env)
  | Expr.ident name => (AList.lookup name env).isSome

theorem typeCheckExpr_isClosedExpr (expr : Expr) (h : (typeCheckExpr expr env) = true) : (isClosedExpr expr env) := match expr with
  | Expr.true => by
    apply h
  | Expr.false => by
    apply h
  | Expr.nand left right => by
    unfold typeCheckExpr at h
    unfold isClosedExpr
    simp [Bool.coe_and_iff] at h
    simp [Bool.coe_and_iff]
    have l := And.left h
    have r := And.right h

    have lp := by apply (typeCheckExpr_isClosedExpr left l)
    have rp := by apply (typeCheckExpr_isClosedExpr right r)
    exact ⟨lp, rp⟩
  | Expr.ident name => by
    apply h
