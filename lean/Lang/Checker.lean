import Lang.Ast
import Lang.Helpers
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
      let newVar := insert name vars
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

/-- A statement is closed if accessed variables exist. -/
def isClosedStmt (stmt : Stmt) (vars : Variables) : Bool := (aux stmt vars).isSome
where
  aux stmt vars := match stmt with
    | Stmt.decl name value =>
        if isClosedExpr value vars then
          some (insert name vars)
        else
          none
    | Stmt.assign target value => if target ∈ vars && isClosedExpr value vars then some vars else none
    | Stmt.conditional condition body => if isClosedExpr condition vars && (aux body vars).isSome then some vars else none

/-- A statement has no redeclarations if each declaration uses a unique name. -/
def hasNoRedeclarations (stmt : Stmt) (vars : Variables) : Bool := (aux stmt vars).isSome
where
  aux stmt vars : Option Variables := match stmt with
    | Stmt.decl name _ =>
        if name ∉ vars then
          some (insert name vars)
        else
          none
    | Stmt.assign _ _ => some vars
    | Stmt.conditional _ body => aux body vars

/-! ## Proofs -/

/-- If Expr.nand is type checked, then lhs is type checked too. -/
lemma typeCheckExpr_nandLeft (h : typeCheckExpr (Expr.nand left right) vars) : typeCheckExpr left vars := by
  unfold typeCheckExpr at h
  simp only [Bool.and_eq_true] at h
  apply And.left at h
  exact h

/-- If Expr.nand is type checked, then rhs is type checked too. -/
lemma typeCheckExpr_nandRight (h : typeCheckExpr (Expr.nand left right) vars) : typeCheckExpr right vars := by
  unfold typeCheckExpr at h
  simp only [Bool.and_eq_true] at h
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
  · simp only [hn, ite_false, Option.isSome_none, not_false_eq_true, ite_true, Option.isSome_some] at h
    by_cases ht : typeCheckExpr value vars
    · simp only [ht, ite_true, Option.isSome_some] at h
      assumption
    · simp only [ht, ite_false, Option.isSome_none] at h
  ·  simp only [hn, ite_false, Option.isSome_none] at h

/-- If Stmt.assign is type checked, then the name exists in the `vars` set. -/
lemma typeCheckStmt_targetExists (h : isTypeCheckedStmt (Stmt.assign target value) vars) : target ∈ vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : target ∈ vars
  · assumption
  · simp only [hn, ite_false, Option.isSome_none, decide_False, Bool.false_and] at h

/-- If Stmt.assign is type checked, then the value is type checked too. -/
lemma typeCheckStmt_assignValue (h : isTypeCheckedStmt (Stmt.assign target value) vars) : typeCheckExpr value vars := by
  have cond := typeCheckStmt_targetExists h
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  simp only [cond, decide_True, Bool.true_and] at h
  apply Option.isSome_if.mp h

/-- If Stmt.conditional is type checked, then the condition is type checked too. -/
lemma typeCheckStmt_conditionalCond (h : isTypeCheckedStmt (Stmt.conditional condition body) vars) : typeCheckExpr condition vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : typeCheckExpr condition vars && Option.isSome (typeCheckStmt body vars)
  · exact Bool.and_elim_left hn
  · simp only [hn, ite_false, Option.isSome_none] at h

/-- If Stmt.conditional is type checked, then the body is type checked too. -/
lemma typeCheckStmt_conditionalBody (h : isTypeCheckedStmt (Stmt.conditional condition body) vars) : isTypeCheckedStmt body vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : typeCheckExpr condition vars && Option.isSome (typeCheckStmt body vars)
  · exact Bool.and_elim_right hn
  · simp only [hn, ite_false, Option.isSome_none] at h

/-- Given that the type checker accepts the expression, we know that the expression is closed. -/
theorem typeCheckExpr_isClosedExpr (h : typeCheckExpr expr vars) : (isClosedExpr expr vars) := match expr with
  | Expr.true => by
      apply h
  | Expr.false => by
      apply h
  | Expr.nand left right => by
      have l := typeCheckExpr_nandLeft h
      have r := typeCheckExpr_nandRight h

      unfold isClosedExpr
      simp only [Bool.and_eq_true]

      have lp := typeCheckExpr_isClosedExpr l
      have rp := typeCheckExpr_isClosedExpr r

      exact ⟨lp, rp⟩
  | Expr.ident _ => by
      apply h

/-- Given that the type checker accepts the statement, we know that the statement is closed. -/
theorem typeCheckStmt_isClosedStmt (stmt : Stmt) (h : isTypeCheckedStmt stmt vars) : (isClosedStmt stmt vars) := match stmt with
    | Stmt.decl name value => by
        unfold isTypeCheckedStmt at h
        unfold typeCheckStmt at h
        unfold isClosedStmt
        unfold isClosedStmt.aux

        by_cases hn : name ∉ vars
        · simp only [hn, ite_false, Option.isSome_none, not_false_eq_true, ite_true, Option.isSome_some] at h
          have cond := Option.isSome_if.mp h
          have condClosed := typeCheckExpr_isClosedExpr cond
          simp only [ite_true, Option.isSome_some, ite_false, Option.isSome_none, *]
        · simp only [hn, ite_false, Option.isSome_none] at h
    | Stmt.assign target value => by
        unfold isTypeCheckedStmt at h
        unfold typeCheckStmt at h
        unfold isClosedStmt
        unfold isClosedStmt.aux

        by_cases hn : target ∉ vars
        · simp only [ite_false, Option.isSome_none, decide_False, Bool.false_and, *] at h
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨l, r⟩ := Option.isSome_if.mp h
          have valueClosed := typeCheckExpr_isClosedExpr r
          simp only [ite_true, Option.isSome_some, decide_True, Bool.and_self, *]
    | Stmt.conditional condition body => by
        unfold isTypeCheckedStmt at h
        unfold typeCheckStmt at h
        unfold isClosedStmt
        unfold isClosedStmt.aux

        simp only [Bool.and_eq_true] at h
        obtain ⟨cond, r⟩ := Option.isSome_if.mp h
        simp only [Bool.and_eq_true]
        rw [← isTypeCheckedStmt] at r
        clear h
        have condClosed := typeCheckExpr_isClosedExpr cond

        apply typeCheckStmt_isClosedStmt at r
        unfold isClosedStmt at r
        simp only [ite_true, Option.isSome_some, and_self, *]
decreasing_by sorry -- TODO: no clue how to prove termination

/-- Given that the type checker accepts the statement, we know there are no redeclared variables in the statement. -/
theorem typeCheckStmt_hasNoRedeclarations (stmt : Stmt) (h : isTypeCheckedStmt stmt vars) : hasNoRedeclarations stmt vars := match stmt with
    | Stmt.decl name _ => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold hasNoRedeclarations
      unfold hasNoRedeclarations.aux

      split
      · simp only [Option.isSome_some, ite_true]
      · case _ ht =>
        simp only [ht, ite_false, Option.isSome_none] at h
    | Stmt.assign _ _ => by
      unfold hasNoRedeclarations
      apply Eq.refl
    | Stmt.conditional _ body => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold hasNoRedeclarations
      unfold hasNoRedeclarations.aux

      simp only [Bool.and_eq_true] at h
      have ⟨l, r⟩ := Option.isSome_if.mp h
      have bodyNoRedecl := typeCheckStmt_hasNoRedeclarations body r
      clear h r l

      unfold hasNoRedeclarations at bodyNoRedecl
      assumption
