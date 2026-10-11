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

/-- Semantic correspondence on an explicit admissible set of inputs.
No behavior is asserted outside `valid`; source errors and divergence remain possible there. -/
@[expose] def CorrespondsOn {a b : Ty} (ha : DataShape a) (hb : DataShape b)
    (valid : a.Native → Prop) (meaning : Computation (.arrow a.core b.core))
    (implementation : a.Native → b.Native) : Prop :=
  ∀ x, valid x → DomainResult.applyContinuous meaning (encodeData ha x) =
    encodeData hb (implementation x)

namespace CorrespondsOn

variable {a b : Ty} {ha : DataShape a} {hb : DataShape b}
  {valid : a.Native → Prop} {meaning : Computation (.arrow a.core b.core)}
  {implementation : a.Native → b.Native}

/-- Restrict an admissibility profile without changing source or implementation. -/
theorem mono (h : CorrespondsOn ha hb valid meaning implementation)
    {valid' : a.Native → Prop} (hvalid : ∀ x, valid' x → valid x) :
    CorrespondsOn ha hb valid' meaning implementation :=
  fun x hx => h x (hvalid x hx)

/-- An implementation equality is needed only on the certified domain. -/
theorem congr (h : CorrespondsOn ha hb valid meaning implementation)
    {other : a.Native → b.Native} (he : ∀ x, valid x → implementation x = other x) :
    CorrespondsOn ha hb valid meaning other := by
  intro x hx
  rw [h x hx, he x hx]

/-- Preconditions and postconditions transfer when the precondition implies admissibility. -/
theorem contract_iff (h : CorrespondsOn ha hb valid meaning implementation)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop)
    (admissible : ∀ x, pre x → valid x) :
    DataMeaningContract ha meaning pre post ↔ ∀ x, pre x → post x (implementation x) := by
  have hr (x : a.Native) (hx : pre x) : Represents b (implementation x)
      (DomainResult.applyContinuous meaning (encodeData ha x)) := by
    rw [h x (admissible x hx)]
    exact represents_encodeData hb _
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    have he := Represents.functional hb hy (hr x hx)
    simpa only [he] using hp
  · intro hp x hx
    exact ⟨implementation x, hr x hx, hp x hx⟩

/-- A source Boolean proposition is true exactly when its native counterpart is true.
Truth here means a fully defined `true`, never error or divergence. -/
theorem property_iff {meaning : Computation (.arrow a.core .bit)}
    {implementation : a.Native → Bool}
    (h : CorrespondsOn ha .bit valid meaning implementation) (x : a.Native) (hx : valid x) :
    DomainResult.applyContinuous meaning (encodeData ha x) = encodeData .bit true ↔
      implementation x = true := by
  rw [h x hx]
  constructor
  · intro he
    exact DiscreteOrder.mk.inj (DomainResult.value_inj.mp he)
  · intro he
    exact congrArg (encodeData .bit) he

end CorrespondsOn

/-- A total native function and its all-input semantic representation theorem. -/
structure CertifiedMeaning {a b : Ty} (ha : DataShape a) (hb : DataShape b) where
  /-- The source function's potentially partial denotation. -/
  meaning : Computation (.arrow a.core b.core)
  /-- The total native function used in specifications. -/
  implementation : a.Native → b.Native
  /-- Every represented input produces the entire represented native result. -/
  correct : ∀ x, DomainResult.applyContinuous meaning (encodeData ha x) =
    encodeData hb (implementation x)

/-- An all-input certificate supplies every restricted admissibility profile. -/
theorem CertifiedMeaning.correspondsOn {a b : Ty} {ha : DataShape a} {hb : DataShape b}
    (f : CertifiedMeaning ha hb) (valid : a.Native → Prop) :
    CorrespondsOn ha hb valid f.meaning f.implementation := fun x _ => f.correct x

/-- Preconditions and postconditions transfer in both directions through the certificate. -/
theorem CertifiedMeaning.contract_iff {a b : Ty} {ha : DataShape a} {hb : DataShape b}
    (f : CertifiedMeaning ha hb) (g : a.Native → b.Native)
    (h : ∀ x, f.implementation x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataMeaningContract ha f.meaning pre post ↔ ∀ x, pre x → post x (g x) :=
  ((f.correspondsOn pre).congr (fun x _ => h x)).contract_iff pre post (fun _ hx => hx)

end Interop.Cryptol.Finite
