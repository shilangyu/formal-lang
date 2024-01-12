import Mathlib.Tactic
import Mathlib.Data.List.AList
import Mathlib.Data.Finset.Basic

/-!
# Helpers

This module stores helper lemmas, functions, utils, etc.
-/

/-! ## Definitions -/

instance AListToString [Repr α] [∀ a, Repr (β a)] : ToString (@AList α β) where
  toString l := "{" ++ (l.entries |> List.map (fun e => s!"{reprStr e.fst}: {reprStr e.snd}") |> String.intercalate ", ") ++ "}"

/-- Returns a finite set of keys of an association list. -/
def keySet {α : Type} {β : α → Type} (a : AList β) : Finset α :=
  Finset.mk (Multiset.ofList a.keys) a.nodupKeys

/-- Given a proof that key ∈ assocList, lookups the key without fail. -/
def AList.get [DecidableEq α] (key : α) (assocList : AList β) (h : key ∈ assocList) : β key :=
  have isSome : (assocList.lookup key).isSome := by exact AList.lookup_isSome.mpr h

  match assocList.lookup key, isSome with
    | some v, _ => v


/-! ## Lemmas -/

@[simp] lemma Option.isSome_isNone_contr (h1 : Option.isSome t) (h2 : Option.isNone t) : False := by
  unfold isSome at h1
  split at h1
  · simp only [isNone_some] at h2
  · simp only at h1

@[simp] lemma Option.isSome_if {p : Prop} {_ : Decidable p} : Option.isSome (if p then some v else none) ↔ p := by
  apply Iff.intro
  · intro h
    split at h
    · simp only [*]
    · case _ ht =>
      simp only [Option.isSome_none] at h
  · intro h
    simp only [ite_true, isSome_some, h]

@[simp] lemma Option.some_eq_some : some t = some b ↔ t = b := by simp only [Option.some.injEq]

@[simp] lemma Option.eqSome_if {p : Prop} {_ : Decidable p} : (if p then some v else none) = some t ↔ p ∧ t = v := by
  apply Iff.intro
  · intro h
    split at h
    · simp only [true_and, *]
      apply Option.some_eq_some.mp h.symm
    · case _ ht =>
      contradiction
  · intro h
    split
    · apply Option.some_eq_some.mpr h.2.symm
    · case _ ht => exact ht h.1

@[simp] lemma Option.eqSome_else {p : Prop} {_ : Decidable p} : (if p then none else some v) = some t ↔ ¬p ∧ t = v := by
  apply Iff.intro
  · intro h
    split at h
    · contradiction
    · case _ ht =>
      simp only [ht, not_false_eq_true, true_and]
      apply Option.some_eq_some.mp h.symm
  · intro h
    split
    · case _ ht => exact h.1 ht
    · apply Option.some_eq_some.mpr h.2.symm

@[simp] lemma Option.isNone_false_isSome : Option.isNone o = false ↔ Option.isSome o := by
  cases o <;> simp only [isNone_none, isSome_none, isNone_some, isSome_some]

@[simp] private lemma List.notIn_cons (h : a ∉ b :: bs) : a ∉ bs := by
  simp only [Bool.not_eq_true, mem_cons] at h
  intro p
  exact h (Or.inr p)

@[simp] private lemma List.erase_notIn {a : α} {l : List α} {_ : DecidableEq α} (h : a ∉ l) : List.erase l a = l := by
  unfold List.erase
  split
  · rfl
  · split
    · simp_all only [List.mem_cons, beq_iff_eq, true_or, not_true_eq_false]
    · simp only [List.cons.injEq, true_and]
      exact (List.erase_notIn (List.notIn_cons h))

@[simp] lemma AList.insert_set_preservation {_ : DecidableEq α} {map : AList β} {key : α} {value : β key} : Insert.insert key (keySet map) = keySet (AList.insert key value map) := by
  unfold keySet
  unfold Insert.insert
  unfold Finset.instInsertFinset
  simp only [Finset.mem_val, Multiset.mem_coe, Multiset.coe_ndinsert, keys_insert, Finset.mk.injEq,
    Multiset.coe_eq_coe]

  by_cases key ∈ (keys map)
  · case _ h =>
    have t := List.perm_cons_erase h
    apply List.Perm.symm
    apply (List.Perm.trans t.symm)
    unfold Insert.insert
    unfold List.instInsertList
    simp only [h, List.mem_cons, or_true, not_true_eq_false, List.insert_of_mem, List.Perm.refl]
  · case _ h =>
    rewrite [List.erase_notIn h]
    unfold Insert.insert
    unfold List.instInsertList
    simp only [h, List.mem_cons, or_false, not_false_eq_true, List.insert_of_not_mem, List.Perm.refl]
