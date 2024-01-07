import Mathlib.Data.List.AList

/-!
# Allocator

Simple bump allocator which manages Locs and their underlying memory. We prove properties about allocation.
-/

/-! ## Definitions -/

/-- A memory location represented as a natural number. Basically a newtype. -/
structure Loc where
  loc : Nat
deriving Repr, DecidableEq

instance : Max Loc where
  max a b := if a.loc > b.loc then a else b

/-- The memory maps variable locations to values. -/
abbrev Memory := @AList Loc (fun _ => Bool)

def alloc (mem : Memory) (v : Bool) : Loc × Memory :=
  let uniqueLoc := mem.keys.maximum?.getD (Loc.mk 0)

  (uniqueLoc, mem.insert uniqueLoc v)

/-! ## Proofs -/
