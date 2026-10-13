/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Finsupp.Basic

/-!
# Kleisli composition of finitely supported families of linear maps

A finitely supported family `p : α →₀ (X →ₗ[R] Y)` assigns a linear map to each label in `α`,
with all but finitely many labels sent to zero. `Finsupp.lbind` is Kleisli composition for the
free-module-style monad on such families: `(p.lbind k) b = ∑ a, k a b ∘ₗ p a`, with unit
`Finsupp.single a LinearMap.id`. `Finsupp.ltotal` sums a family over its labels.

The unit and associativity laws (`Finsupp.single_id_lbind`, `Finsupp.lbind_single_id`,
`Finsupp.lbind_assoc`) are stated heterogeneously in the modules and hold in this generality,
before any positivity or trace condition is imposed on the linear maps.
-/

public section

namespace Finsupp

variable {α β γ : Type*} {R : Type*} [Semiring R]
  {X Y Z W : Type*} [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z] [AddCommMonoid W]
  [Module R X] [Module R Y] [Module R Z] [Module R W]

/-! ## Kleisli composition -/

/-- Precomposition distributes over a finitely supported sum of linear maps. -/
theorem sum_linearMap_comp {M : Type*} [Zero M] (p : α →₀ M) (g : α → M → Y →ₗ[R] Z)
    (φ : X →ₗ[R] Y) : p.sum g ∘ₗ φ = p.sum fun a m ↦ g a m ∘ₗ φ := by
  ext x
  simp [Finsupp.sum, LinearMap.sum_apply]

/-- Kleisli composition of finitely supported families of linear maps: the family whose member
at `b` is `∑ a, k a b ∘ₗ p a`. With `Finsupp.single a LinearMap.id` as unit this is the bind of
the free-module-style monad on finitely supported families of linear maps, and the monad laws
hold before any positivity or trace condition is imposed. -/
@[expose]
noncomputable def lbind (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z)) :
    β →₀ (X →ₗ[R] Z) :=
  p.sum fun a φ ↦ (k a).mapRange (fun ψ ↦ ψ ∘ₗ φ) (LinearMap.zero_comp φ)

/-- The member of a Kleisli composite at `b` sums the composites `k a b ∘ₗ p a`. -/
theorem lbind_apply (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z)) (b : β) :
    p.lbind k b = p.sum fun a φ ↦ k a b ∘ₗ φ := by
  simp [lbind, Finsupp.sum_apply]

/-- The member of a Kleisli composite at `b` as a sum over the support of the first family. -/
theorem lbind_apply_eq_sum (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z)) (b : β) :
    p.lbind k b = ∑ a ∈ p.support, k a b ∘ₗ p a :=
  lbind_apply p k b

/-- The member of a Kleisli composite at `b` as a sum over a finite type of labels. -/
theorem lbind_apply_eq_sum_univ [Fintype α] (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z))
    (b : β) : p.lbind k b = ∑ a, k a b ∘ₗ p a :=
  (lbind_apply p k b).trans <| sum_fintype _ _ fun _ ↦ LinearMap.comp_zero _

/-- Binding the zero family gives the zero family. -/
@[simp]
theorem zero_lbind (k : α → β →₀ (Y →ₗ[R] Z)) : (0 : α →₀ (X →ₗ[R] Y)).lbind k = 0 :=
  sum_zero_index

/-- Left unit law: binding the unit family at `a` selects `k a`. -/
@[simp]
theorem single_id_lbind (a : α) (k : α → β →₀ (X →ₗ[R] Y)) :
    (single a LinearMap.id).lbind k = k a := by
  ext b : 1
  rw [lbind_apply, sum_single_index (h := fun a φ ↦ k a b ∘ₗ φ) (LinearMap.comp_zero _),
    LinearMap.comp_id]

/-- Binding with unit families relabelled by `f` is `Finsupp.mapDomain f`. -/
theorem lbind_single_id_comp (p : α →₀ (X →ₗ[R] Y)) (f : α → β) :
    p.lbind (fun a ↦ single (f a) LinearMap.id) = p.mapDomain f := by
  simp [lbind, mapDomain, mapRange_single]

/-- Right unit law: binding with the unit families is the identity. -/
@[simp]
theorem lbind_single_id (p : α →₀ (X →ₗ[R] Y)) :
    p.lbind (fun a ↦ single a LinearMap.id) = p := by
  simpa using lbind_single_id_comp p id

/-- Associativity of Kleisli composition. -/
theorem lbind_assoc (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z))
    (l : β → γ →₀ (Z →ₗ[R] W)) :
    (p.lbind k).lbind l = p.lbind fun a ↦ (k a).lbind l := by
  ext c : 1
  rw [lbind_apply, lbind_apply, lbind,
    sum_sum_index (fun _ ↦ LinearMap.comp_zero _) (fun _ _ _ ↦ LinearMap.comp_add _ _ _)]
  refine Finsupp.sum_congr fun a _ ↦ ?_
  rw [sum_mapRange_index (fun _ ↦ LinearMap.comp_zero _), lbind_apply, sum_linearMap_comp]
  simp only [LinearMap.comp_assoc]

/-- The support of a Kleisli composite lies in the union of the supports of the continuations
reached from the support of the first family. -/
theorem support_lbind_subset [DecidableEq β] (p : α →₀ (X →ₗ[R] Y))
    (k : α → β →₀ (Y →ₗ[R] Z)) :
    (p.lbind k).support ⊆ p.support.biUnion fun a ↦ (k a).support :=
  support_sum.trans <| Finset.biUnion_mono fun _ _ ↦ support_mapRange

/-! ## Total of a family -/

/-- The sum of a finitely supported family of linear maps over its labels. -/
@[expose]
noncomputable def ltotal (p : α →₀ (X →ₗ[R] Y)) : X →ₗ[R] Y :=
  p.sum fun _ φ ↦ φ

/-- The total of a family as a sum over its support. -/
theorem ltotal_eq_sum (p : α →₀ (X →ₗ[R] Y)) : p.ltotal = ∑ a ∈ p.support, p a :=
  rfl

/-- The total of a family applied to a vector sums the values of its members. -/
theorem ltotal_apply (p : α →₀ (X →ₗ[R] Y)) (x : X) : p.ltotal x = ∑ a ∈ p.support, p a x :=
  LinearMap.sum_apply ..

/-- The zero family has total zero. -/
@[simp]
theorem ltotal_zero : (0 : α →₀ (X →ₗ[R] Y)).ltotal = 0 :=
  sum_zero_index

/-- A family with a single member has that member as total. -/
@[simp]
theorem ltotal_single (a : α) (φ : X →ₗ[R] Y) : (single a φ).ltotal = φ :=
  sum_single_index rfl

/-- The total of a family summed over a finite type of labels. -/
theorem ltotal_eq_sum_univ [Fintype α] (p : α →₀ (X →ₗ[R] Y)) : p.ltotal = ∑ a, p a :=
  sum_fintype _ _ fun _ ↦ rfl

/-- The total of a Kleisli composite sums the totals of the continuations after each member of
the first family. -/
theorem ltotal_lbind (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z)) :
    (p.lbind k).ltotal = p.sum fun a φ ↦ (k a).ltotal ∘ₗ φ := by
  rw [ltotal, lbind, sum_sum_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  refine Finsupp.sum_congr fun a _ ↦ ?_
  rw [sum_mapRange_index (fun _ ↦ rfl), ltotal, sum_linearMap_comp]

/-- Relabelling a family does not change its total. -/
@[simp]
theorem ltotal_mapDomain (p : α →₀ (X →ₗ[R] Y)) (f : α → β) :
    (p.mapDomain f).ltotal = p.ltotal :=
  sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-! ## Transport along additive maps of linear maps -/

section mapRange

variable {X' Y' Z' : Type*} [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
  [Module R X'] [Module R Y'] [Module R Z']

/-- An additive map of linear maps commutes with the total of a family. -/
theorem ltotal_mapRange (F : (X →ₗ[R] Y) → (X' →ₗ[R] Y')) (hF : F 0 = 0)
    (hF_add : ∀ φ ψ, F (φ + ψ) = F φ + F ψ) (p : α →₀ (X →ₗ[R] Y)) :
    (p.mapRange F hF).ltotal = F p.ltotal := by
  rw [ltotal, sum_mapRange_index (fun _ ↦ rfl), ltotal]
  exact (map_finsuppSum (⟨⟨F, hF⟩, hF_add⟩ : (X →ₗ[R] Y) →+ (X' →ₗ[R] Y')) p _).symm

/-- Maps of linear maps that jointly preserve composition, the last of them additive, commute
with Kleisli composition. -/
theorem mapRange_lbind (F : (X →ₗ[R] Y) → (X' →ₗ[R] Y')) (G : (Y →ₗ[R] Z) → (Y' →ₗ[R] Z'))
    (H : (X →ₗ[R] Z) → (X' →ₗ[R] Z')) (hF : F 0 = 0) (hG : G 0 = 0) (hH : H 0 = 0)
    (hH_add : ∀ φ ψ, H (φ + ψ) = H φ + H ψ) (hcomp : ∀ ψ φ, H (ψ ∘ₗ φ) = G ψ ∘ₗ F φ)
    (p : α →₀ (X →ₗ[R] Y)) (k : α → β →₀ (Y →ₗ[R] Z)) :
    (p.lbind k).mapRange H hH = (p.mapRange F hF).lbind fun a ↦ (k a).mapRange G hG := by
  ext b : 1
  rw [mapRange_apply, lbind_apply, lbind_apply,
    sum_mapRange_index (fun _ ↦ LinearMap.comp_zero _)]
  simp only [mapRange_apply, ← hcomp]
  exact map_finsuppSum (⟨⟨H, hH⟩, hH_add⟩ : (X →ₗ[R] Z) →+ (X' →ₗ[R] Z')) p _

end mapRange

end Finsupp
