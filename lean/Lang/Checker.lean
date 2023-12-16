import Lang.Ast
import Mathlib.Data.Finset.Basic

/-!
# Static checker

This module focuses on static properties of a program. Meaning, the analysis
that can be performed on source code without actually evaluating it.
-/

/-! ## Definitions -/

/-- Variables is a set of currently defined variable names. -/
abbrev Variables := Finset Name

/-- Returns true if the expression is well-formed. -/
def typeCheckExpr (expr : Expr) (vars : Variables) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.true
  | Expr.nand left right => (typeCheckExpr left vars) && (typeCheckExpr right vars)
  | Expr.ident name => name ∈ vars
  -- | Expr.ref of => Bool.true
  -- | Expr.deref of => Bool.true

def typeCheckStmt (stmt : Stmt) (vars : Variables) : Option Variables := match stmt with
    | Stmt.decl name value =>
      if name ∉ vars then
        let newVar := (insert name vars)
        if typeCheckExpr value vars then
          some newVar
        else
          none
      else none
    | Stmt.assign target value => if target ∈ vars && typeCheckExpr value vars then some vars else none
    | Stmt.conditional condition body => if typeCheckExpr condition vars && (typeCheckStmt body vars).isSome then some vars else none

/-- The assertion that `typeCheckStmt` accepted the input, ie it is not `none`. -/
def isTypeCheckedStmt (stmt : Stmt) (vars : Variables) := (typeCheckStmt stmt vars).isSome

/-! ## Properties -/

/-- An expression is closed if accessed variables exist. -/
def isClosedExpr (expr : Expr) (vars : Variables) : Bool := match expr with
  | Expr.true => Bool.true
  | Expr.false => Bool.true
  | Expr.nand left right => (isClosedExpr left vars) && (isClosedExpr right vars)
  | Expr.ident name => name ∈ vars

/-! ## Theorems -/

/-- If Expr.nand is type checked, then lhs is type checked too. -/
lemma typeCheckExpr_nandLeft (h : typeCheckExpr (Expr.nand left right) vars) : typeCheckExpr left vars := by
  unfold typeCheckExpr at h
  simp [Bool.coe_and_iff] at h
  apply And.left at h
  exact h

/-- If Expr.nand is type checked, then rhs is type checked too. -/
lemma typeCheckExpr_nandRight (h : typeCheckExpr (Expr.nand left right) vars) : typeCheckExpr right vars := by
  unfold typeCheckExpr at h
  simp [Bool.coe_and_iff] at h
  apply And.right at h
  exact h

/-- If Expr.ident is type checked, then the name exists in the `vars` set. -/
lemma typeCheckExpr_ident (h : typeCheckExpr (Expr.ident name) vars) : name ∈ vars := by
  unfold typeCheckExpr at h
  exact (Bool.coe_decide (name ∈ vars)).mp h

/-- If Stmt.decl is type checked, then the value is type checked too. -/
lemma typeCheckStmt_declValue (h : isTypeCheckedStmt (Stmt.decl name value) vars) : typeCheckExpr value vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : name ∉ vars
  · simp [ite_false, hn] at h
    by_cases ht : typeCheckExpr value vars
    · simp [ite_false, ht] at h
      assumption
    · simp [ite_false, ht] at h
  ·  simp [ite_true, hn] at h

/-- If Stmt.assign is type checked, then the value is type checked too. -/
lemma typeCheckStmt_assignValue (h : isTypeCheckedStmt (Stmt.assign target value) vars) : typeCheckExpr value vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : (decide (target ∈ vars) && typeCheckExpr value vars)
  · simp [ite_false, hn] at h
    exact Bool.and_elim_right hn
  · simp_all only [ite_false, Option.isSome_none]

/-- If Stmt.assign is type checked, then the name exists in the `vars` set. -/
lemma typeCheckStmt_assign (h : isTypeCheckedStmt (Stmt.assign target value) vars) : target ∈ vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : target ∈ vars
  · assumption
  · simp [Bool.false_and, hn] at h

/-- If Stmt.conditional is type checked, then the condition is type checked too. -/
lemma typeCheckStmt_conditionalCond (h : isTypeCheckedStmt (Stmt.conditional condition body) vars) : typeCheckExpr condition vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : typeCheckExpr condition vars && Option.isSome (typeCheckStmt body vars)
  · exact Bool.and_elim_left hn
  · simp [Bool.false_and, hn] at h

/-- If Stmt.conditional is type checked, then the body is type checked too. -/
lemma typeCheckStmt_conditionalBody (h : isTypeCheckedStmt (Stmt.conditional condition body) vars) : isTypeCheckedStmt body vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : typeCheckExpr condition vars && Option.isSome (typeCheckStmt body vars)
  · exact Bool.and_elim_right hn
  · simp [Bool.false_and, hn] at h

/-- Given that the type checker accepts the expression, we know that the expression is closed. -/
theorem typeCheckExpr_isClosedExpr (expr : Expr) (h : (typeCheckExpr expr vars)) : (isClosedExpr expr vars) := match expr with
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
  | Expr.ident _ => by
    apply h
