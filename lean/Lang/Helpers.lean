import Mathlib


/-!
# Helpers

This module stores helper lemmas, functions, utils, etc.
-/

/-! ## Lemmas -/

@[simp] lemma Option.isSome_isNone_contr (h1 : Option.isSome t) (h2 : Option.isNone t) : False := by
  unfold isSome at h1
  split at h1 <;> simp_all
