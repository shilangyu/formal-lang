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
  | Stmt.while condition body => if typeCheckExpr condition vars && (typeCheckStmt body vars).isSome then some vars else none
  | Stmt.seq left right => match typeCheckStmt left vars with
    | some vars => typeCheckStmt right vars
    | none => none
  | Stmt.free name => if name ∈ vars then some vars else none

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
    | Stmt.while condition body => if isClosedExpr condition vars && (aux body vars).isSome then some vars else none
    | Stmt.seq left right => match aux left vars with
      | some vars => aux right vars
      | none => none
    | Stmt.free name => if name ∈ vars then some vars else none

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
    | Stmt.conditional _ body => if (aux body vars).isSome then some vars else none
    | Stmt.while _ body => if (aux body vars).isSome then some vars else none
    | Stmt.seq left right => match aux left vars with
      | some vars => aux right vars
      | none => none
    | Stmt.free _ => some vars

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

/-- If Stmt.while is type checked, then the condition is type checked too. -/
lemma typeCheckStmt_whileCond (h : isTypeCheckedStmt (Stmt.while condition body) vars) : typeCheckExpr condition vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : typeCheckExpr condition vars && Option.isSome (typeCheckStmt body vars)
  · exact Bool.and_elim_left hn
  · simp only [hn, ite_false, Option.isSome_none] at h

/-- If Stmt.while is type checked, then the body is type checked too. -/
lemma typeCheckStmt_whileBody (h : isTypeCheckedStmt (Stmt.while condition body) vars) : isTypeCheckedStmt body vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : typeCheckExpr condition vars && Option.isSome (typeCheckStmt body vars)
  · exact Bool.and_elim_right hn
  · simp only [hn, ite_false, Option.isSome_none] at h

/-- If Stmt.seq is type checked, then the left side is type checked too. -/
lemma typeCheckStmt_seqLeft (h : isTypeCheckedStmt (Stmt.seq left right) vars) : isTypeCheckedStmt left vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  split at h
  · case _ hn =>
    simp only [isTypeCheckedStmt, hn, Option.isSome_some, ite_true]
  · simp only [Option.isSome_none] at h

/-- If Stmt.seq is type checked, then the right side is type checked too. -/
lemma typeCheckStmt_seqRight (h : isTypeCheckedStmt (Stmt.seq left right) vars) (eq : typeCheckStmt left vars = some newEnv) : isTypeCheckedStmt right newEnv := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  split at h
  · case _ varst hn =>
    have ht : newEnv = varst := by
      simp only [eq, Option.some.injEq] at hn
      assumption
    rw [isTypeCheckedStmt]
    subst ht
    assumption
  · simp only [Option.isSome_none] at h

/-- If Stmt.free is type checked, then the name exists in the `vars` set. -/
lemma typeCheckStmt_freeNameExists (h : isTypeCheckedStmt (Stmt.free name) vars) : name ∈ vars := by
  rw [isTypeCheckedStmt] at h
  unfold typeCheckStmt at h
  by_cases hn : name ∈ vars
  · assumption
  · simp only [hn, ite_false, Option.isSome_none, decide_False, Bool.false_and] at h

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

/-- Given that the type checker accepts the statement, we know that the returned variables are the same as in the `isClosedStmt` property. -/
lemma typeCheckStmt_vars_eq_isClosedStmt (h : isTypeCheckedStmt stmt vars) : typeCheckStmt stmt vars = isClosedStmt.aux stmt vars := match stmt with
  | Stmt.decl name value => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold isClosedStmt.aux

      split at h <;> simp_all only [Option.isSome_if, not_false_eq_true, ite_true]
      · apply Eq.symm
        rw [Option.eqSome_if]
        simp only [and_true]
        apply typeCheckExpr_isClosedExpr h
      · case _ ht =>
        absurd h
        simp only [Option.isSome_none, not_false_eq_true]
  | Stmt.assign target value => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold isClosedStmt.aux

      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_if] at h
      simp only [decide_True, Bool.and_self, ite_true, Bool.true_and, *]
      apply Eq.symm
      rw [Option.eqSome_if]
      simp only [and_true]
      apply typeCheckExpr_isClosedExpr h.2
  | Stmt.conditional condition body | Stmt.while condition body => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold isClosedStmt.aux

      simp only [Bool.and_eq_true, Option.isSome_if] at h
      simp only [decide_True, Bool.and_self, ite_true, Bool.true_and, *]
      apply Eq.symm
      rw [Option.eqSome_if]
      simp only [h, typeCheckExpr_isClosedExpr, Bool.true_and, and_true]
      have q := h.2
      rw [← isTypeCheckedStmt] at q
      apply typeCheckStmt_vars_eq_isClosedStmt at q
      simp_all only
  | Stmt.seq left right => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold isClosedStmt.aux

      split at h
      · case _ varst hq =>
        rw [← isTypeCheckedStmt] at h
        apply typeCheckStmt_vars_eq_isClosedStmt at h

        have hu : Option.isSome (typeCheckStmt left vars) := by simp only [hq, Option.isSome_some]
        rw [← isTypeCheckedStmt] at hu
        apply typeCheckStmt_vars_eq_isClosedStmt at hu

        simp only [hu ▸ hq, h]
      · simp only [Option.isSome_none] at h
  | Stmt.free name => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold isClosedStmt.aux
      rfl
decreasing_by sorry -- TODO: no clue how to prove termination


/-- Given that the type checker accepts the statement, we know that the statement is closed. -/
theorem typeCheckStmt_isClosedStmt (h : isTypeCheckedStmt stmt vars) : (isClosedStmt stmt vars) := by
  have p := typeCheckStmt_vars_eq_isClosedStmt h
  rw [isTypeCheckedStmt] at h
  have o := p ▸ h
  rw [isClosedStmt]
  assumption

/-- Given that the type checker accepts the statement, we know that the returned variables are the same as in the `hasNoRedeclarations` property. -/
theorem typeCheckStmt_vars_eq_hasNoRedeclarations (h : isTypeCheckedStmt stmt vars) : typeCheckStmt stmt vars = hasNoRedeclarations.aux stmt vars := match stmt with
    | Stmt.decl name _ => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold hasNoRedeclarations.aux

      split <;> simp only [ite_eq_left_iff, Bool.not_eq_true, imp_false, Bool.not_eq_false]
      · case _ t =>
        simp only [t, not_false_eq_true, ite_true, Option.isSome_if] at h
        assumption
    | Stmt.assign _ _ => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold hasNoRedeclarations.aux

      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_if] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, ite_eq_left_iff, not_and, Bool.not_eq_true, imp_false, not_forall, Bool.not_eq_false, exists_prop]
      assumption
    | Stmt.conditional _ body | Stmt.while _ body => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold hasNoRedeclarations.aux

      simp only [Bool.and_eq_true] at h
      have ⟨l, r⟩ := Option.isSome_if.mp h
      have bodyNoRedecl := typeCheckStmt_vars_eq_hasNoRedeclarations r
      clear h r

      split
      · case _ ht =>
        simp only [Bool.and_eq_true] at ht
        simp only [bodyNoRedecl ▸ ht.2, ite_true]
      · case _ ht =>
        simp at ht
        have te := Option.isNone_iff_eq_none.mp (bodyNoRedecl ▸ ht l)
        simp only [Option.isSome_none, ite_false, te]
    | Stmt.seq left right => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold hasNoRedeclarations.aux

      split at h
      · case _ varst hq =>
        rw [← isTypeCheckedStmt] at h
        apply typeCheckStmt_vars_eq_hasNoRedeclarations at h

        have hu : Option.isSome (typeCheckStmt left vars) := by simp only [hq, Option.isSome_some]
        rw [← isTypeCheckedStmt] at hu
        apply typeCheckStmt_vars_eq_hasNoRedeclarations at hu

        simp only [hu ▸ hq, h]
      · simp only [Option.isSome_none] at h
    | Stmt.free name => by
      unfold isTypeCheckedStmt at h
      unfold typeCheckStmt at h
      unfold typeCheckStmt
      unfold hasNoRedeclarations.aux
      have t := Option.isSome_if.mp h
      apply Option.eqSome_if.mpr
      simp only [and_true]
      exact t
decreasing_by sorry -- TODO: no idea how to prove termination


/-- Given that the type checker accepts the statement, we know there are no redeclared variables in the statement. -/
theorem typeCheckStmt_hasNoRedeclarations (h : isTypeCheckedStmt stmt vars) : hasNoRedeclarations stmt vars := by
  have p := typeCheckStmt_vars_eq_hasNoRedeclarations h
  rw [isTypeCheckedStmt] at h
  have o := p ▸ h
  rw [hasNoRedeclarations]
  assumption
