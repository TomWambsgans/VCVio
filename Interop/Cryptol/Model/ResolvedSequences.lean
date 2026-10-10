/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.ResolvedLaws

/-!
# Ranges and single-generator comprehensions

These derived constructors retain suspended function arguments and sequence
elements. An empty or ignored generator never adds a demand on its source.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Resolved

/-- A finite integer enumeration with an arbitrary starting integer. -/
@[expose] def Term.range {Γ : List ClosedTy} (start : Int) (n : Nat) :
    Term Γ (.seq (.finite n) .integer) :=
  .sequence n (fun i => .integer (start + (i.val : Int)))

/-- A single-generator comprehension with a suspended element argument. -/
@[expose] def Term.map {Γ : List ClosedTy} {a b : ClosedTy} {l : Length}
    (f : Term Γ (.arrow a b)) (xs : Term Γ (.seq l a)) : Term Γ (.seq l b) :=
  .app (.app (.lam (.lam (.generate l
    (.app (.var (.succ (.succ .zero))) (.index (.var (.succ .zero)) (.var .zero)))))) f) xs

/-- Enumeration exposes precisely the integer assigned to each finite position. -/
theorem denote_range {Γ : List ClosedTy} (start : Int) (n : Nat) (ρ : Environment Γ) :
    denote (Term.range start n) ρ =
      DomainResult.value (fun i : Fin n => DomainResult.value ⟨start + (i.val : Int)⟩) := rfl

/-- Mapping exposes a lazy array even when its function or source is partial. -/
theorem denote_map {Γ : List ClosedTy} {a b : ClosedTy} {l : Length}
    (f : Term Γ (.arrow a b)) (xs : Term Γ (.seq l a)) (ρ : Environment Γ) :
    denote (Term.map f xs) ρ = DomainResult.value (fun i : l.Index =>
      DomainResult.applyContinuous (denote f ρ)
        (Semantics.indexAt (denote xs ρ) (Length.indexNat i))) := rfl

end Interop.Cryptol.Resolved
