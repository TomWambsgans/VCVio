/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Representation

/-!
# Specifications of represented semantic functions

Contract transfer depends on a semantic equality and a faithful representation.
It is independent of the syntax used to produce that meaning. Source-specific
certificates retain their descriptions and supply this common semantic evidence.
-/

public section

namespace Interop.Cryptol.Finite

/-- Total correctness of a semantic function on represented data inputs. -/
@[expose] def DataMeaningContract {a b : Ty} (ha : DataShape a)
    (f : Computation (.arrow a.core b.core))
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) : Prop :=
  ∀ x, pre x → ∃ y, Represents b y
    (DomainResult.applyContinuous f (encodeData ha x)) ∧ post x y

/-- A total native function and its all-input semantic representation theorem. -/
structure CertifiedMeaning {a b : Ty} (ha : DataShape a) (hb : DataShape b) where
  /-- The source function's potentially partial denotation. -/
  meaning : Computation (.arrow a.core b.core)
  /-- The total native function used in specifications. -/
  implementation : a.Native → b.Native
  /-- Every represented input produces the entire represented native result. -/
  correct : ∀ x, DomainResult.applyContinuous meaning (encodeData ha x) =
    encodeData hb (implementation x)

/-- Preconditions and postconditions transfer in both directions through the certificate. -/
theorem CertifiedMeaning.contract_iff {a b : Ty} {ha : DataShape a} {hb : DataShape b}
    (f : CertifiedMeaning ha hb) (g : a.Native → b.Native)
    (h : ∀ x, f.implementation x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataMeaningContract ha f.meaning pre post ↔ ∀ x, pre x → post x (g x) := by
  have hr (x : a.Native) : Represents b (g x)
      (DomainResult.applyContinuous f.meaning (encodeData ha x)) := by
    rw [f.correct, h x]
    exact represents_encodeData hb _
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    have he := Represents.functional hb hy (hr x)
    simpa only [he] using hp
  · intro hp x hx
    exact ⟨g x, hr x, hp x hx⟩

end Interop.Cryptol.Finite
