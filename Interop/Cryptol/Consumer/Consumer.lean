/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Translation.Certified
import Interop.Cryptol.Translation.Finite.Loop
import Interop.Cryptol.Model.ResolvedSequences
import Interop.Cryptol.Model.Recurrence
import Interop.Cryptol.Translation.PolymorphicExamples

/-!
# Independent public API consumer

A separate package supplies its own specification without opening implementation
bodies or importing any cryptographic interpretation.
-/

open Interop.Cryptol Interop.Cryptol.Finite

example {a b : Finite.Ty} {ha : DataShape a} {hb : DataShape b}
    (f : CertifiedFunction ha hb) (g : a.Native → b.Native)
    (h : ∀ x, f.implementation.denote Env.empty x = g x)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataContract ha (Resolved.lower f.source) pre post ↔ ∀ x, pre x → post x (g x) :=
  f.contract_iff g h pre post

example {Γ : List ClosedTy} (start : Int) (n : Nat) (ρ : Environment Γ) :
    Resolved.denote (Resolved.Term.range start n) ρ =
      DomainResult.value (fun i : Fin n => DomainResult.value ⟨start + (i.val : Int)⟩) :=
  Resolved.denote_range start n ρ

example {Γ Δ : List Finite.Ty} {a : Finite.Ty} (e : Finite.Term Γ a)
    (θ : Finite.signature.Substitution Γ Δ) (ρ : Env Δ) :
    Finite.Term.denote (e.subst θ) ρ = e.denote (fun _ v => Finite.Term.denote (θ v) ρ) :=
  Finite.Term.denote_subst e θ ρ

example {Γ : List Finite.Ty} {a : Finite.Ty}
    (step : (n : Nat) → Finite.Term (.seq n a :: Γ) a) (n bound : Nat)
    (h : ∀ i < n, (step i).nodeCount ≤ bound) :
    (Finite.Term.prefixTable step n).nodeCount ≤ 1 + n * (bound + 5) :=
  Finite.Term.nodeCount_prefixTable_le step n bound h

example (n : Nat) (pre : (BitVec n × BitVec n) → Prop)
    (post : (BitVec n × BitVec n) → BitVec n → Prop) :
    DataMeaningContract (b := .word n) (.prod (.word n) (.word n))
      (PolymorphicExamples.xorCertificate.meaningAt n).meaning pre post ↔
        ∀ x, pre x → post x (x.1 ^^^ x.2) :=
  PolymorphicExamples.xor_contract n pre post

example {w : Polymorphic.Scope} {Γ : List w.ValueSort}
    {a b : PolyTy w.numbers w.types} (ρ : w.Assignment)
    (body : Polymorphic.Term w (.mono a :: Γ) (.mono b))
    (value : Polymorphic.Term w Γ (.mono a)) (η : Polymorphic.Env ρ Γ) :
    (Polymorphic.Term.app (.lam body) value).denote ρ η =
      body.denote ρ (Polymorphic.Env.cons ρ (η, value.denote ρ η)) :=
  Polymorphic.Term.denote_beta ρ body value η
