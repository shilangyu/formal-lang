import Mathlib.Tactic
import Mathlib.Data.List.AList
import Mathlib.Data.Finset.Basic

/-!
# Helpers

This module stores helper lemmas, functions, utils, etc.
-/

/-! ## Functions -/

instance AListToString [Repr α] [∀ a, Repr (β a)] : ToString (@AList α β) where
  toString l := "{" ++ (l.entries |> List.map (fun e => s!"{reprStr e.fst}: {reprStr e.snd}") |> String.intercalate ", ") ++ "}"

/-- Returns a finite set of keys of an association list. -/
def keySet {α : Type} {β : α → Type} (a : @AList α β) : Finset α :=
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
      simp only [ht, false_and]
      assumption
  · intro h
    split
    · apply Option.some_eq_some.mpr h.2.symm
    · simp [*] at h
