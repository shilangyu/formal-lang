import Mathlib.Tactic


/-!
# Helpers

This module stores helper lemmas, functions, utils, etc.
-/

/-! ## Lemmas -/

@[simp] lemma Option.isSome_isNone_contr (h1 : Option.isSome t) (h2 : Option.isNone t) : False := by
  unfold isSome at h1
  split at h1
  · simp only [isNone_some] at h2
  · simp only at h1

@[simp] lemma Option.isSome_if {p : Prop} {_ : Decidable p} (h : Option.isSome (if p then some v else none)) : p := by
  split at h
  · simp only [*]
  · case _ ht =>
    simp only [Option.isSome_none] at h
