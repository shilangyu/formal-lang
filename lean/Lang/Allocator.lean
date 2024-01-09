import Mathlib.Data.List.AList
import Lang.Ast

/-!
# Allocator

Simple bump allocator which manages Locs and their underlying memory. We prove properties about allocation.
-/

/-! ## Definitions -/

/-- A memory location represented as a natural number. Basically a newtype of Nat. -/
structure Loc where
  loc : Nat
deriving Repr, DecidableEq

instance : Max Loc where
  max a b := if a.loc > b.loc then a else b

private abbrev Env := @AList Name (fun _ => Loc)

/-- The memory maps variable locations to values. -/
abbrev Memory := @AList Loc (fun _ => Bool)

def alloc (env : Env) (mem : Memory) (v : Bool) : Loc × Memory :=
  let maxLoc := env.entries.map Sigma.snd |> List.maximum? |> (Option.getD ·  (Loc.mk 0))
  let uniqueLoc := Loc.mk (maxLoc.loc + 1)

  (uniqueLoc, mem.insert uniqueLoc v)

/-! ## Proofs -/
