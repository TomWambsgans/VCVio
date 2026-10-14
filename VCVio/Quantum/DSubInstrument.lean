/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.Finsupp.ToDFinsupp
public import VCVio.Quantum.SubInstrument

/-!
# Dependent subinstruments

A dependent subinstrument from the system with basis `A`, with classical outcomes `i : ι`, has
output system `B i` on outcome `i`: after a measurement the register may depend on the outcome,
for example a qubit kept on one outcome and discarded on another. It is a finitely supported
family of completely positive maps `branch i : MatrixMap A (B i)` whose traces sum to at most the
trace of the input on positive semidefinite inputs.

The branches have different codomains, so they cannot be summed as maps. Trace nonincrease is
stated through the trace functional `Quantum.MatrixMap.familyTrace`, `ρ ↦ ∑ i, trace (branch i ρ)`.
Mathematically a dependent subinstrument is one completely positive, trace-nonincreasing map into
the direct sum `⊕ i, M_{B i}` of matrix algebras. It is not a map into the matrix algebra on the
disjoint union `Σ i, B i`, which would allow coherences between outcomes.

Sequencing is Kleisli composition of branch families (`Quantum.MatrixMap.familyBind`), with unit
the single identity branch `Quantum.DSubInstrument.ret`. The unit and associativity laws hold for
families of arbitrary linear maps, and are equalities of structures for dependent subinstruments.

## The constant-codomain case

`Quantum.SubInstrument A B α` is exactly the case of a constant output system:
`Quantum.SubInstrument.equivD : SubInstrument A B α ≃ DSubInstrument A α (fun _ ↦ B)`. The
equivalence sends `pure`, `bind`, `map`, `fail`, `frame` and `ofKraus` to `ret`, `bind`, `map`,
`fail`, `frame` and `ofKraus` (`Quantum.SubInstrument.toD_pure`, `toD_bind`, `toD_map`,
`toD_fail`, `toD_frame`, `toD_ofKraus`), and losslessness to losslessness
(`Quantum.SubInstrument.lossless_toD_iff`). For a constant codomain the trace functional of a
branch family is the trace after the total map (`Quantum.SubInstrument.familyTrace_toDFinsupp`),
so the trace condition of a dependent subinstrument is the core condition
`Quantum.MatrixMap.IsTNI` on the total map (`Quantum.SubInstrument.isTNI_ltotal_iff`).

## Main definitions

* `Quantum.MatrixMap.familyTrace`, `Quantum.MatrixMap.familyBind`: the trace functional and
  Kleisli composition of finitely supported families of matrix maps with outcome-dependent
  codomains.
* `Quantum.DSubInstrument A ι B`: dependent subinstruments, with `ret`, `bind`, `map`, `fail`,
  `frame` and `ofKraus`.
* `Quantum.DSubInstrument.Lossless`: the trace functional is the trace.
* `Quantum.SubInstrument.toD`, `Quantum.DSubInstrument.toSubInstrument`,
  `Quantum.SubInstrument.equivD`: the constant-codomain case.
-/

public section

open scoped ComplexOrder
open Matrix

namespace DFinsupp

variable {ι : Type*} {β : ι → Type*} {γ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ]

/-- `DFinsupp.sumAddHom` as a sum over any finite set outside which the function vanishes. -/
theorem sumAddHom_apply_eq_sum_of_forall_notMem [DecidableEq ι] (φ : ∀ i, β i →+ γ) (f : Π₀ i, β i)
    {s : Finset ι} (hs : ∀ i ∉ s, f i = 0) : sumAddHom φ f = ∑ i ∈ s, φ i (f i) := by
  classical
  rw [sumAddHom_apply]
  exact sum_of_support_subset
    (fun i hi ↦ Classical.byContradiction fun h ↦ mem_support_iff.mp hi (hs i h))
    fun i _ ↦ map_zero (φ i)

end DFinsupp

namespace Quantum

namespace MatrixMap

/-! ## Families of matrix maps with outcome-dependent codomains -/

section familyBind

variable {A : Type*} {ι κ μ : Type*} {B : ι → Type*} {C : κ → Type*} {E : μ → Type*}

open Classical in
/-- Kleisli composition of finitely supported families of matrix maps with outcome-dependent
codomains: the family whose member at `c` is `∑ i, Ψ i c ∘ₗ Φ i`. This is the dependent analogue
of `Finsupp.lbind`, with unit `DFinsupp.single i LinearMap.id`. -/
@[expose]
noncomputable def familyBind (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) : Π₀ c, MatrixMap A (C c) :=
  DFinsupp.sumAddHom (β := fun i ↦ MatrixMap A (B i)) (fun i ↦
    { toFun φ := (Ψ i).mapRange (fun _ ψ ↦ ψ ∘ₗ φ) fun _ ↦ LinearMap.zero_comp φ
      map_zero' := DFinsupp.ext fun c ↦ by simp
      map_add' φ φ' := DFinsupp.ext fun c ↦ by simp [LinearMap.comp_add] }) Φ

/-- The member of a Kleisli composite at `c`, as a sum over any finite set outside which the first
family vanishes. -/
theorem familyBind_apply_of_forall_notMem (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) {s : Finset ι} (hs : ∀ i ∉ s, Φ i = 0) (c : κ) :
    familyBind Φ Ψ c = ∑ i ∈ s, Ψ i c ∘ₗ Φ i := by
  classical
  rw [familyBind, DFinsupp.sumAddHom_apply_eq_sum_of_forall_notMem _ _ hs,
    DFinsupp.finsetSum_apply]
  rfl

/-- The member of a Kleisli composite at `c`, as a sum over the support of the first family. -/
theorem familyBind_apply [DecidableEq ι] [∀ i (x : MatrixMap A (B i)), Decidable (x ≠ 0)]
    (Φ : Π₀ i, MatrixMap A (B i)) (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) (c : κ) :
    familyBind Φ Ψ c = ∑ i ∈ Φ.support, Ψ i c ∘ₗ Φ i :=
  familyBind_apply_of_forall_notMem Φ Ψ (fun _ ↦ DFinsupp.notMem_support_iff.mp) c

/-- The member of a Kleisli composite at `c`, as a sum over a finite type of labels. -/
theorem familyBind_apply_univ [Fintype ι] (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) (c : κ) :
    familyBind Φ Ψ c = ∑ i, Ψ i c ∘ₗ Φ i :=
  familyBind_apply_of_forall_notMem Φ Ψ (fun i hi ↦ absurd (Finset.mem_univ i) hi) c

/-- A Kleisli composite vanishes at `c` when every continuation reached from the first family
vanishes at `c`. -/
theorem familyBind_apply_eq_zero (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) {s : Finset ι} (hs : ∀ i ∉ s, Φ i = 0) {c : κ}
    (hc : ∀ i ∈ s, Ψ i c = 0) : familyBind Φ Ψ c = 0 := by
  rw [familyBind_apply_of_forall_notMem Φ Ψ hs]
  exact Finset.sum_eq_zero fun i hi ↦ by rw [hc i hi, LinearMap.zero_comp]

/-- Binding the zero family gives the zero family. -/
@[simp]
theorem zero_familyBind (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) :
    familyBind (0 : Π₀ i, MatrixMap A (B i)) Ψ = 0 := by
  rw [familyBind]
  exact map_zero _

/-- Binding the zero continuations gives the zero family. -/
@[simp]
theorem familyBind_zero (Φ : Π₀ i, MatrixMap A (B i)) :
    familyBind Φ (fun _ ↦ 0 : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) = 0 :=
  DFinsupp.ext fun c ↦ by
    classical
    rw [familyBind_apply]
    simp

/-- Left unit law: binding the unit family at `i` selects the continuation at `i`. -/
@[simp]
theorem single_id_familyBind [DecidableEq ι] (i : ι)
    (Ψ : (j : ι) → Π₀ c, MatrixMap (B j) (C c)) :
    familyBind (DFinsupp.single i (LinearMap.id : MatrixMap (B i) (B i))) Ψ = Ψ i :=
  DFinsupp.ext fun c ↦ by
    rw [familyBind_apply_of_forall_notMem
      (DFinsupp.single i (LinearMap.id : MatrixMap (B i) (B i))) Ψ (s := {i})
      (fun j hj ↦ DFinsupp.single_eq_of_ne (Finset.notMem_singleton.mp hj)),
      Finset.sum_singleton, DFinsupp.single_eq_same, LinearMap.comp_id]

/-- Right unit law: binding with the unit families is the identity. -/
@[simp]
theorem familyBind_single_id [DecidableEq ι] (Φ : Π₀ i, MatrixMap A (B i)) :
    familyBind Φ (fun i ↦ DFinsupp.single i (LinearMap.id : MatrixMap (B i) (B i))) = Φ := by
  classical
  refine DFinsupp.ext fun c ↦ ?_
  rw [familyBind_apply, Finset.sum_eq_single c]
  · rw [DFinsupp.single_eq_same, LinearMap.id_comp]
  · intro i _ hi
    rw [DFinsupp.single_eq_of_ne (Ne.symm hi), LinearMap.zero_comp]
  · intro hc
    rw [DFinsupp.notMem_support_iff.mp hc, LinearMap.comp_zero]

/-- Associativity of Kleisli composition. -/
theorem familyBind_assoc (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) (Χ : (c : κ) → Π₀ m, MatrixMap (C c) (E m)) :
    familyBind (familyBind Φ Ψ) Χ = familyBind Φ fun i ↦ familyBind (Ψ i) Χ := by
  classical
  have hT : ∀ i ∈ Φ.support, ∀ c ∉ Φ.support.biUnion fun i ↦ (Ψ i).support, Ψ i c = 0 :=
    fun i hi c hc ↦ DFinsupp.notMem_support_iff.mp fun h ↦ hc (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
  refine DFinsupp.ext fun m ↦ LinearMap.ext fun ρ ↦ ?_
  rw [familyBind_apply_of_forall_notMem _ Χ fun c hc ↦ familyBind_apply_eq_zero Φ Ψ
      (fun _ ↦ DFinsupp.notMem_support_iff.mp) fun i hi ↦ hT i hi c hc,
    familyBind_apply Φ (fun i ↦ familyBind (Ψ i) Χ) m]
  simp only [familyBind_apply Φ Ψ, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [familyBind_apply_of_forall_notMem (Ψ i) Χ (hT i hi) m]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]

/-- Postcomposing every member of a Kleisli composite with the amplification by `R` gives the
Kleisli composite of the amplified families. -/
theorem familyBind_mapRange_amplify (R : Type*) (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) :
    (familyBind Φ Ψ).mapRange (fun _ Θ ↦ Θ.amplify R) (fun _ ↦ amplify_zero) =
      familyBind (Φ.mapRange (fun _ Θ ↦ Θ.amplify R) fun _ ↦ amplify_zero)
        fun i ↦ (Ψ i).mapRange (fun _ Θ ↦ Θ.amplify R) fun _ ↦ amplify_zero := by
  classical
  refine DFinsupp.ext fun c ↦ ?_
  have hs : ∀ i ∉ Φ.support,
      (Φ.mapRange (fun _ Θ ↦ Θ.amplify R) fun _ ↦ amplify_zero) i = 0 := fun i hi ↦ by
    rw [DFinsupp.mapRange_apply, DFinsupp.notMem_support_iff.mp hi, amplify_zero]
  rw [DFinsupp.mapRange_apply, familyBind_apply_of_forall_notMem _ _ hs, familyBind_apply,
    amplify_sum]
  rfl

end familyBind

section familyTrace

variable {A : Type*} {ι κ : Type*} {B : ι → Type*} [∀ i, Fintype (B i)] {C : κ → Type*}

open Classical in
/-- The trace functional of a finitely supported family of matrix maps with outcome-dependent
codomains: `ρ ↦ ∑ i, trace (Φ i ρ)`. It is the trace on the direct sum `⊕ i, M_{B i}` after the
map whose components are the members of the family. -/
@[expose]
noncomputable def familyTrace (Φ : Π₀ i, MatrixMap A (B i)) : Matrix A A ℂ →ₗ[ℂ] ℂ :=
  DFinsupp.sumAddHom (β := fun i ↦ MatrixMap A (B i)) (fun i ↦
    { toFun Ψ := Matrix.traceLinearMap (B i) ℂ ℂ ∘ₗ Ψ
      map_zero' := LinearMap.comp_zero _
      map_add' Ψ Ψ' := LinearMap.comp_add Ψ Ψ' _ }) Φ

/-- The trace functional as a sum over any finite set outside which the family vanishes. -/
theorem familyTrace_apply_of_forall_notMem (Φ : Π₀ i, MatrixMap A (B i)) {s : Finset ι}
    (hs : ∀ i ∉ s, Φ i = 0) (ρ : Matrix A A ℂ) :
    familyTrace Φ ρ = ∑ i ∈ s, (Φ i ρ).trace := by
  classical
  rw [familyTrace, DFinsupp.sumAddHom_apply_eq_sum_of_forall_notMem _ _ hs, LinearMap.sum_apply]
  rfl

/-- The trace functional as a sum over the support of the family. -/
theorem familyTrace_apply [DecidableEq ι] [∀ i (x : MatrixMap A (B i)), Decidable (x ≠ 0)]
    (Φ : Π₀ i, MatrixMap A (B i)) (ρ : Matrix A A ℂ) :
    familyTrace Φ ρ = ∑ i ∈ Φ.support, (Φ i ρ).trace :=
  familyTrace_apply_of_forall_notMem Φ (fun _ ↦ DFinsupp.notMem_support_iff.mp) ρ

/-- The trace functional as a sum over a finite type of labels. -/
theorem familyTrace_apply_univ [Fintype ι] (Φ : Π₀ i, MatrixMap A (B i)) (ρ : Matrix A A ℂ) :
    familyTrace Φ ρ = ∑ i, (Φ i ρ).trace :=
  familyTrace_apply_of_forall_notMem Φ (fun i hi ↦ absurd (Finset.mem_univ i) hi) ρ

/-- The trace functional of the zero family is zero. -/
@[simp]
theorem familyTrace_zero : familyTrace (0 : Π₀ i, MatrixMap A (B i)) = 0 := by
  rw [familyTrace]
  exact map_zero _

/-- The trace functional of a family with a single member is the trace after that member. -/
@[simp]
theorem familyTrace_single [DecidableEq ι] (i : ι) (Φ : MatrixMap A (B i)) :
    familyTrace (DFinsupp.single i Φ) = Matrix.traceLinearMap (B i) ℂ ℂ ∘ₗ Φ := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [familyTrace_apply_of_forall_notMem (DFinsupp.single i Φ) (s := {i})
    (fun j hj ↦ DFinsupp.single_eq_of_ne (Finset.notMem_singleton.mp hj)) ρ,
    Finset.sum_singleton, DFinsupp.single_eq_same]
  rfl

omit [∀ i, Fintype (B i)] in
/-- The trace functional of a Kleisli composite sums, over the members of the first family, the
trace functional of the continuation after that member. -/
theorem familyTrace_familyBind [∀ c, Fintype (C c)] (Φ : Π₀ i, MatrixMap A (B i))
    (Ψ : (i : ι) → Π₀ c, MatrixMap (B i) (C c)) {s : Finset ι} (hs : ∀ i ∉ s, Φ i = 0)
    (ρ : Matrix A A ℂ) :
    familyTrace (familyBind Φ Ψ) ρ = ∑ i ∈ s, familyTrace (Ψ i) (Φ i ρ) := by
  classical
  have hT : ∀ i ∈ s, ∀ c ∉ s.biUnion fun i ↦ (Ψ i).support, Ψ i c = 0 :=
    fun i hi c hc ↦ DFinsupp.notMem_support_iff.mp fun h ↦ hc (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
  rw [familyTrace_apply_of_forall_notMem _ fun c hc ↦ familyBind_apply_eq_zero Φ Ψ hs
    fun i hi ↦ hT i hi c hc]
  simp only [familyBind_apply_of_forall_notMem Φ Ψ hs, LinearMap.sum_apply, LinearMap.comp_apply,
    Matrix.trace_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i hi ↦
    (familyTrace_apply_of_forall_notMem (Ψ i) (hT i hi) (Φ i ρ)).symm

/-- The trace functional of a family amplified by `R` sums the trace functional of the family on
the diagonal ancilla blocks. -/
theorem familyTrace_mapRange_amplify {R : Type*} [Fintype R] (Φ : Π₀ i, MatrixMap A (B i))
    (ρ : Matrix (A × R) (A × R) ℂ) :
    familyTrace (Φ.mapRange (fun _ Θ ↦ Θ.amplify R) fun _ ↦ amplify_zero) ρ =
      ∑ r, familyTrace Φ (ρ.submatrix (·, r) (·, r)) := by
  classical
  have hs : ∀ i ∉ Φ.support,
      (Φ.mapRange (fun _ Θ ↦ Θ.amplify R) fun _ ↦ amplify_zero) i = 0 := fun i hi ↦ by
    rw [DFinsupp.mapRange_apply, DFinsupp.notMem_support_iff.mp hi, amplify_zero]
  rw [familyTrace_apply_of_forall_notMem _ hs]
  simp only [DFinsupp.mapRange_apply, trace_amplify_apply, familyTrace_apply Φ]
  exact Finset.sum_comm

end familyTrace

end MatrixMap

/-! ## Dependent subinstruments -/

/-- A dependent subinstrument from the system with basis `A`, with classical outcomes `i : ι` and
output system `B i` on outcome `i`: a finitely supported family of completely positive maps
`branch i : MatrixMap A (B i)` whose traces sum to at most the trace of the input on positive
semidefinite inputs. It is one completely positive, trace-nonincreasing map into the direct sum
`⊕ i, M_{B i}`. -/
@[ext]
structure DSubInstrument (A : Type*) [Fintype A] (ι : Type*) (B : ι → Type*)
    [∀ i, Fintype (B i)] where
  /-- The map applied to the state on outcome `i`; zero outside finitely many outcomes. -/
  branch : Π₀ i, MatrixMap A (B i)
  /-- Every branch is completely positive. -/
  isCP_branch : ∀ i, (branch i).IsCP
  /-- The traces of the branches sum to at most the trace of the input on positive semidefinite
  inputs. -/
  trace_le : ∀ ρ : Matrix A A ℂ, ρ.PosSemidef → (MatrixMap.familyTrace branch ρ).re ≤ ρ.trace.re

namespace DSubInstrument

variable {A : Type*} [Fintype A] {ι κ μ : Type*} {B : ι → Type*} [∀ i, Fintype (B i)]
  {C : κ → Type*} [∀ c, Fintype (C c)] {E : μ → Type*} [∀ m, Fintype (E m)]

/-! ### Trace bounds -/

/-- Each branch sends positive semidefinite matrices to positive semidefinite matrices. -/
theorem posSemidef_branch_apply (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch i ρ).PosSemidef :=
  (p.isCP_branch i).posSemidef hρ

/-- On a positive semidefinite input, each branch has nonnegative trace. -/
theorem trace_re_branch_apply_nonneg (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ (p.branch i ρ).trace.re :=
  (p.posSemidef_branch_apply i hρ).trace_re_nonneg

/-- On a positive semidefinite input, the traces of the branches over any finite set outside
which the branches vanish sum to at most the trace of the input. -/
theorem sum_trace_re_le (p : DSubInstrument A ι B) {s : Finset ι}
    (hs : ∀ i ∉ s, p.branch i = 0) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑ i ∈ s, (p.branch i ρ).trace.re ≤ ρ.trace.re := by
  have h := p.trace_le ρ hρ
  rwa [MatrixMap.familyTrace_apply_of_forall_notMem _ hs, Complex.re_sum] at h

/-- On a positive semidefinite input, the traces of the branches over the support sum to at most
the trace of the input. -/
theorem sum_support_trace_re_le [DecidableEq ι] [∀ i (x : MatrixMap A (B i)), Decidable (x ≠ 0)]
    (p : DSubInstrument A ι B) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑ i ∈ p.branch.support, (p.branch i ρ).trace.re ≤ ρ.trace.re :=
  p.sum_trace_re_le (fun _ ↦ DFinsupp.notMem_support_iff.mp) hρ

/-- On a positive semidefinite input, each branch has trace at most that of the input. -/
theorem trace_re_branch_apply_le (p : DSubInstrument A ι B) (i : ι) {ρ : Matrix A A ℂ}
    (hρ : ρ.PosSemidef) : (p.branch i ρ).trace.re ≤ ρ.trace.re := by
  classical
  refine le_trans ?_ (p.sum_trace_re_le (s := insert i p.branch.support)
    (fun j hj ↦ DFinsupp.notMem_support_iff.mp fun h ↦ hj (Finset.mem_insert_of_mem h)) hρ)
  exact Finset.single_le_sum (f := fun j ↦ (p.branch j ρ).trace.re)
    (fun j _ ↦ p.trace_re_branch_apply_nonneg j hρ) (Finset.mem_insert_self i _)

/-! ### Return -/

section ret

variable (B)

open Classical in
/-- **Return.** The dependent subinstrument on `B i` with the single outcome `i` and the identity
branch. -/
@[expose]
noncomputable def ret (i : ι) : DSubInstrument (B i) ι B where
  branch := DFinsupp.single i LinearMap.id
  isCP_branch j := by
    obtain rfl | h := eq_or_ne j i
    · rw [DFinsupp.single_eq_same]
      exact .id
    · rw [DFinsupp.single_eq_of_ne h]
      exact .zero
  trace_le ρ _ := by
    rw [MatrixMap.familyTrace_single]
    exact le_rfl

/-- The branch of `ret B i` at `i` is the identity map. -/
@[simp]
theorem branch_ret_self (i : ι) : (ret B i).branch i = LinearMap.id := by
  classical
  exact DFinsupp.single_eq_same

/-- The branch of `ret B i` away from `i` is zero. -/
@[simp]
theorem branch_ret_of_ne {i j : ι} (h : j ≠ i) : (ret B i).branch j = 0 := by
  classical
  exact DFinsupp.single_eq_of_ne h

/-- The branch family of `ret B i` is the identity map at `i` and zero elsewhere. -/
theorem branch_ret [DecidableEq ι] (i : ι) :
    (ret B i).branch = DFinsupp.single i LinearMap.id := by
  refine DFinsupp.ext fun j ↦ ?_
  obtain rfl | h := eq_or_ne j i
  · rw [branch_ret_self, DFinsupp.single_eq_same]
  · rw [branch_ret_of_ne B h, DFinsupp.single_eq_of_ne h]

end ret

/-! ### Sequencing -/

/-- **Sequencing.** Run `p`; on outcome `i`, run `k i` on the system `B i`. The branch at `c` is
`∑ i, (k i).branch c ∘ₗ p.branch i`. -/
@[expose]
protected noncomputable def bind (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) : DSubInstrument A κ C where
  branch := MatrixMap.familyBind p.branch fun i ↦ (k i).branch
  isCP_branch c := by
    classical
    rw [MatrixMap.familyBind_apply]
    exact .sum _ fun i _ ↦ ((k i).isCP_branch c).comp (p.isCP_branch i)
  trace_le ρ hρ := by
    classical
    rw [MatrixMap.familyTrace_familyBind p.branch _ (fun _ ↦ DFinsupp.notMem_support_iff.mp),
      Complex.re_sum]
    exact (Finset.sum_le_sum fun i _ ↦ (k i).trace_le _ (p.posSemidef_branch_apply i hρ)).trans
      (p.sum_support_trace_re_le hρ)

/-- The branch family of a composite is the Kleisli composite of the branch families. -/
theorem branch_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C) :
    (p.bind k).branch = MatrixMap.familyBind p.branch fun i ↦ (k i).branch :=
  rfl

/-- The branch of a composite at `c`, as a sum over any finite set outside which the branches of
the first subinstrument vanish. -/
theorem branch_bind_apply_of_forall_notMem (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) {s : Finset ι} (hs : ∀ i ∉ s, p.branch i = 0)
    (c : κ) : (p.bind k).branch c = ∑ i ∈ s, (k i).branch c ∘ₗ p.branch i :=
  MatrixMap.familyBind_apply_of_forall_notMem _ _ hs c

/-- The branch of a composite at `c` sums, over the outcomes `i` of the first subinstrument, the
branch of the continuation at `c` after the branch at `i`. -/
theorem branch_bind_apply [DecidableEq ι] [∀ i (x : MatrixMap A (B i)), Decidable (x ≠ 0)]
    (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) :
    (p.bind k).branch c = ∑ i ∈ p.branch.support, (k i).branch c ∘ₗ p.branch i :=
  MatrixMap.familyBind_apply _ _ c

/-- The branch of a composite at `c` as a sum over a finite type of intermediate outcomes. -/
theorem branch_bind_apply_univ [Fintype ι] (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) :
    (p.bind k).branch c = ∑ i, (k i).branch c ∘ₗ p.branch i :=
  MatrixMap.familyBind_apply_univ _ _ c

/-- The trace functional of a composite sums, over the outcomes of the first subinstrument, the
trace functional of the continuation after the corresponding branch. -/
theorem familyTrace_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    {s : Finset ι} (hs : ∀ i ∉ s, p.branch i = 0) (ρ : Matrix A A ℂ) :
    MatrixMap.familyTrace (p.bind k).branch ρ =
      ∑ i ∈ s, MatrixMap.familyTrace (k i).branch (p.branch i ρ) :=
  MatrixMap.familyTrace_familyBind _ _ hs ρ

/-! ### Monad laws -/

/-- Left unit law: returning `i` and then running `k` is `k i`. -/
@[simp]
theorem ret_bind (i : ι) (k : (j : ι) → DSubInstrument (B j) κ C) : (ret B i).bind k = k i := by
  classical
  ext1
  rw [branch_bind, branch_ret]
  exact MatrixMap.single_id_familyBind i _

/-- Right unit law: running `p` and then returning its outcome is `p`. -/
@[simp]
theorem bind_ret (p : DSubInstrument A ι B) : p.bind (ret B) = p := by
  classical
  ext1
  rw [branch_bind]
  simp only [branch_ret]
  exact MatrixMap.familyBind_single_id _

/-- Sequencing of dependent subinstruments is associative. -/
theorem bind_assoc (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (l : (c : κ) → DSubInstrument (C c) μ E) :
    (p.bind k).bind l = p.bind fun i ↦ (k i).bind l :=
  DSubInstrument.ext <| MatrixMap.familyBind_assoc _ _ _

/-! ### Reindexing outcomes -/

/-- Reindex the outcomes of `p` along `f : ι → κ` when its output system on outcome `i` is
`C (f i)`: outcome `i` is reported as `f i`, and the branches of outcomes with the same image are
summed. -/
@[expose]
protected noncomputable def map (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    DSubInstrument A κ C :=
  p.bind fun i ↦ ret C (f i)

/-- Reindexing along `f` is sequencing with `fun i ↦ ret C (f i)`. -/
theorem map_eq_bind_ret (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    p.map f = p.bind fun i ↦ ret C (f i) :=
  rfl

/-- Reindexing along the identity changes nothing. -/
@[simp]
theorem map_id (p : DSubInstrument A ι B) : p.map (C := B) id = p :=
  bind_ret p

/-- Reindexing twice is reindexing along the composite. -/
theorem map_map {ν : Type*} {F : ν → Type*} [∀ n, Fintype (F n)] (f : ι → κ) (g : κ → ν)
    (p : DSubInstrument A ι fun i ↦ F (g (f i))) :
    (p.map (C := fun c ↦ F (g c)) f).map g = p.map (C := F) (g ∘ f) := by
  simp only [map_eq_bind_ret, bind_assoc, ret_bind, Function.comp_apply]

/-- Reindexing `ret` along `f` is `ret` at the image. -/
@[simp]
theorem map_ret (f : ι → κ) (i : ι) : (ret (fun i ↦ C (f i)) i).map (C := C) f = ret C (f i) :=
  ret_bind i _

/-- Reindexing after sequencing is sequencing with reindexed continuations. -/
theorem map_bind {ν : Type*} {F : ν → Type*} [∀ n, Fintype (F n)] (f : κ → ν)
    (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ fun c ↦ F (f c)) :
    (p.bind k).map f = p.bind fun i ↦ (k i).map f :=
  bind_assoc _ _ _

/-! ### Failure -/

/-- The dependent subinstrument with no branches: it fails on every input. -/
@[expose]
protected noncomputable def fail : DSubInstrument A ι B where
  branch := 0
  isCP_branch _ := .zero
  trace_le ρ hρ := by simpa using hρ.trace_re_nonneg

/-- The failing subinstrument has no branches. -/
@[simp]
theorem branch_fail : (DSubInstrument.fail : DSubInstrument A ι B).branch = 0 :=
  rfl

/-- Failure absorbs every continuation. -/
@[simp]
theorem fail_bind (k : (i : ι) → DSubInstrument (B i) κ C) :
    (DSubInstrument.fail : DSubInstrument A ι B).bind k = DSubInstrument.fail :=
  DSubInstrument.ext <| MatrixMap.zero_familyBind _

/-- Sequencing with failing continuations fails. -/
@[simp]
theorem bind_fail (p : DSubInstrument A ι B) :
    (p.bind fun _ ↦ DSubInstrument.fail : DSubInstrument A κ C) = DSubInstrument.fail :=
  DSubInstrument.ext <| MatrixMap.familyBind_zero _

/-! ### Framing by an ancilla -/

/-- The action of a dependent subinstrument on a system extended by an ancilla with basis `R`
that it leaves untouched, on the right as in `Quantum.SubInstrument.frame`: every branch is
amplified by `R`. -/
@[expose]
noncomputable def frame (p : DSubInstrument A ι B) (R : Type*) [Fintype R] :
    DSubInstrument (A × R) ι fun i ↦ B i × R where
  branch := p.branch.mapRange (fun _ Φ ↦ Φ.amplify R) fun _ ↦ MatrixMap.amplify_zero
  isCP_branch i := by
    rw [DFinsupp.mapRange_apply]
    exact (p.isCP_branch i).amplify
  trace_le ρ hρ := by
    rw [MatrixMap.familyTrace_mapRange_amplify, Complex.re_sum,
      MatrixMap.trace_eq_sum_trace_submatrix ρ, Complex.re_sum]
    exact Finset.sum_le_sum fun r _ ↦ p.trace_le _ (hρ.submatrix _)

section frame

variable (R : Type*) [Fintype R]

/-- Each branch of a framed dependent subinstrument is the amplified branch. -/
@[simp]
theorem branch_frame_apply (p : DSubInstrument A ι B) (i : ι) :
    (p.frame R).branch i = (p.branch i).amplify R :=
  rfl

/-- Framing `ret B i` gives `ret` on the extended systems. -/
@[simp]
theorem frame_ret (i : ι) : (ret B i).frame R = ret (fun j ↦ B j × R) i := by
  refine DSubInstrument.ext <| DFinsupp.ext fun j ↦ ?_
  rw [branch_frame_apply]
  obtain rfl | h := eq_or_ne j i
  · rw [branch_ret_self, branch_ret_self, MatrixMap.amplify_id]
  · rw [branch_ret_of_ne B h, branch_ret_of_ne _ h, MatrixMap.amplify_zero]

/-- Framing commutes with sequencing. -/
theorem frame_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C) :
    (p.bind k).frame R = (p.frame R).bind fun i ↦ (k i).frame R :=
  DSubInstrument.ext <| MatrixMap.familyBind_mapRange_amplify R p.branch fun i ↦ (k i).branch

/-- Framing commutes with reindexing outcomes. -/
theorem frame_map (f : ι → κ) (p : DSubInstrument A ι fun i ↦ C (f i)) :
    (p.map f).frame R = (p.frame R).map (C := fun c ↦ C c × R) f := by
  simp only [map_eq_bind_ret, frame_bind, frame_ret]

/-- Framing the failing subinstrument gives the failing subinstrument. -/
@[simp]
theorem frame_fail :
    (DSubInstrument.fail : DSubInstrument A ι B).frame R = DSubInstrument.fail :=
  DSubInstrument.ext <| DFinsupp.ext fun i ↦ by simp

end frame

/-! ### Losslessness -/

/-- A dependent subinstrument is lossless when its trace functional is the trace: the traces of
its branches sum to the trace of the input, so it never fails. This is the analogue of
`Quantum.SubInstrument.Lossless`, trace preservation of the total map. -/
@[expose]
def Lossless (p : DSubInstrument A ι B) : Prop :=
  ∀ ρ : Matrix A A ℂ, MatrixMap.familyTrace p.branch ρ = ρ.trace

variable (B) in
/-- Returning a value is lossless. -/
theorem lossless_ret (i : ι) : (ret B i).Lossless := fun ρ ↦ by
  classical
  rw [branch_ret, MatrixMap.familyTrace_single]
  rfl

/-- Sequencing lossless dependent subinstruments is lossless. -/
theorem Lossless.bind {p : DSubInstrument A ι B} {k : (i : ι) → DSubInstrument (B i) κ C}
    (hp : p.Lossless) (hk : ∀ i, (k i).Lossless) : (p.bind k).Lossless := fun ρ ↦ by
  classical
  rw [familyTrace_bind p k (fun _ ↦ DFinsupp.notMem_support_iff.mp), ← hp ρ,
    MatrixMap.familyTrace_apply]
  exact Finset.sum_congr rfl fun i _ ↦ hk i _

/-- Reindexing the outcomes of a lossless dependent subinstrument is lossless. -/
theorem Lossless.map {f : ι → κ} {p : DSubInstrument A ι fun i ↦ C (f i)} (hp : p.Lossless) :
    (p.map f).Lossless :=
  hp.bind fun i ↦ lossless_ret C (f i)

/-- Framing a lossless dependent subinstrument is lossless. -/
theorem Lossless.frame {p : DSubInstrument A ι B} (hp : p.Lossless) (R : Type*) [Fintype R] :
    (p.frame R).Lossless := fun ρ ↦ by
  rw [MatrixMap.trace_eq_sum_trace_submatrix ρ]
  exact (MatrixMap.familyTrace_mapRange_amplify p.branch ρ).trans
    (Finset.sum_congr rfl fun r _ ↦ hp _)

/-- A lossless dependent subinstrument satisfies its trace condition with equality. -/
theorem Lossless.sum_trace_eq {p : DSubInstrument A ι B} (hp : p.Lossless) {s : Finset ι}
    (hs : ∀ i ∉ s, p.branch i = 0) (ρ : Matrix A A ℂ) :
    ∑ i ∈ s, (p.branch i ρ).trace = ρ.trace := by
  rw [← MatrixMap.familyTrace_apply_of_forall_notMem _ hs, hp ρ]

/-! ### Measurements -/

/-- The measurement with Kraus operators `K i : Matrix (B i) A ℂ`, one per outcome, whose output
system depends on the outcome, subject to the completeness relation `∑ i, (K i)ᴴ * K i = 1`. The
branch at `i` is `ρ ↦ K i * ρ * (K i)ᴴ`. -/
@[expose]
noncomputable def ofKraus [Fintype ι] [DecidableEq A] (K : (i : ι) → Matrix (B i) A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) : DSubInstrument A ι B where
  branch := DFinsupp.equivFunOnFintype.symm fun i ↦ MatrixMap.conj (K i)
  isCP_branch i := MatrixMap.isCP_conj (K i)
  trace_le ρ _ := by
    refine (congrArg Complex.re ?_).le
    rw [MatrixMap.familyTrace_apply_univ]
    change ∑ i, (MatrixMap.conj (K i) ρ).trace = ρ.trace
    simp_rw [MatrixMap.trace_conj_apply]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

/-- The branch of a Kraus measurement at `i` is the Kraus map of `K i`. -/
@[simp]
theorem branch_ofKraus_apply [Fintype ι] [DecidableEq A] (K : (i : ι) → Matrix (B i) A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (i : ι) : (ofKraus K hK).branch i = MatrixMap.conj (K i) :=
  rfl

/-- A measurement with a complete family of Kraus operators is lossless. -/
theorem lossless_ofKraus [Fintype ι] [DecidableEq A] (K : (i : ι) → Matrix (B i) A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) : (ofKraus K hK).Lossless := fun ρ ↦ by
  rw [MatrixMap.familyTrace_apply_univ]
  simp_rw [branch_ofKraus_apply, MatrixMap.trace_conj_apply]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

end DSubInstrument

/-! ## Subinstruments are the constant-codomain case -/

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

omit [Fintype A] in
/-- For a constant codomain, the trace functional of a branch family is the trace after the total
map. -/
theorem familyTrace_toDFinsupp (Φ : α →₀ MatrixMap A B) :
    MatrixMap.familyTrace Φ.toDFinsupp = Matrix.traceLinearMap B ℂ ℂ ∘ₗ Finsupp.ltotal Φ := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [MatrixMap.familyTrace_apply_of_forall_notMem Φ.toDFinsupp (s := Φ.support)
    fun a ha ↦ (Finsupp.notMem_support_iff.mp ha : Φ a = 0)]
  change _ = (Finsupp.ltotal Φ ρ).trace
  rw [Finsupp.ltotal_apply, Matrix.trace_sum]
  rfl

/-- For a constant codomain, the trace condition of a dependent subinstrument is trace
nonincrease of the total map, `Quantum.MatrixMap.IsTNI`. -/
theorem isTNI_ltotal_iff (Φ : α →₀ MatrixMap A B) :
    MatrixMap.IsTNI (Finsupp.ltotal Φ) ↔
      ∀ ρ : Matrix A A ℂ, ρ.PosSemidef →
        (MatrixMap.familyTrace Φ.toDFinsupp ρ).re ≤ ρ.trace.re := by
  rw [familyTrace_toDFinsupp]
  rfl

/-- For a constant codomain, the trace functional of a branch family is the trace exactly when
the total map is trace preserving. -/
theorem isTP_ltotal_iff (Φ : α →₀ MatrixMap A B) :
    MatrixMap.IsTP (Finsupp.ltotal Φ) ↔
      ∀ ρ : Matrix A A ℂ, MatrixMap.familyTrace Φ.toDFinsupp ρ = ρ.trace := by
  rw [familyTrace_toDFinsupp]
  rfl

/-- A subinstrument as a dependent subinstrument with constant output system. -/
@[expose]
noncomputable def toD (p : SubInstrument A B α) : DSubInstrument A α fun _ ↦ B where
  branch := p.branch.toDFinsupp
  isCP_branch := p.isCP_branch
  trace_le := (isTNI_ltotal_iff p.branch).mp p.isTNI_total

/-- The branch family of `toD p` is the branch family of `p`. -/
@[simp]
theorem branch_toD (p : SubInstrument A B α) : (toD p).branch = p.branch.toDFinsupp :=
  rfl

/-- The branch of `toD p` at `a` is the branch of `p` at `a`. -/
theorem branch_toD_apply (p : SubInstrument A B α) (a : α) : (toD p).branch a = p.branch a :=
  rfl

end SubInstrument

namespace DSubInstrument

variable {A B : Type*} [Fintype A] [Fintype B] {α : Type*}

/-- A dependent subinstrument with constant output system as a subinstrument. -/
@[expose]
noncomputable def toSubInstrument (q : DSubInstrument A α fun _ ↦ B) : SubInstrument A B α where
  branch := Finsupp.ofSupportFinite (fun a ↦ q.branch a) q.branch.finite_support
  isCP_branch := q.isCP_branch
  isTNI_total := by
    have h : (Finsupp.ofSupportFinite (fun a ↦ q.branch a) q.branch.finite_support).toDFinsupp =
        q.branch := DFinsupp.ext fun _ ↦ rfl
    rw [SubInstrument.isTNI_ltotal_iff, h]
    exact q.trace_le

/-- The branch of `q.toSubInstrument` at `a` is the branch of `q` at `a`. -/
@[simp]
theorem branch_toSubInstrument_apply (q : DSubInstrument A α fun _ ↦ B) (a : α) :
    q.toSubInstrument.branch a = q.branch a :=
  rfl

end DSubInstrument

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-- **Subinstruments are the constant-codomain case of dependent subinstruments.** -/
@[expose]
noncomputable def equivD : SubInstrument A B α ≃ DSubInstrument A α fun _ ↦ B where
  toFun := toD
  invFun := DSubInstrument.toSubInstrument
  left_inv _ := SubInstrument.ext <| Finsupp.ext fun _ ↦ rfl
  right_inv _ := DSubInstrument.ext <| DFinsupp.ext fun _ ↦ rfl

/-- The equivalence `equivD` is `toD`. -/
@[simp]
theorem equivD_apply (p : SubInstrument A B α) : equivD p = toD p :=
  rfl

/-- The inverse of `equivD` is `toSubInstrument`. -/
@[simp]
theorem equivD_symm_apply (q : DSubInstrument A α fun _ ↦ B) :
    equivD.symm q = q.toSubInstrument :=
  rfl

/-- `toSubInstrument` is a left inverse of `toD`. -/
@[simp]
theorem toSubInstrument_toD (p : SubInstrument A B α) : (toD p).toSubInstrument = p :=
  equivD.left_inv p

/-- `toD` is a left inverse of `toSubInstrument`. -/
@[simp]
theorem toD_toSubInstrument (q : DSubInstrument A α fun _ ↦ B) : toD q.toSubInstrument = q :=
  equivD.right_inv q

/-- `toD` is injective. -/
theorem toD_injective : Function.Injective (toD : SubInstrument A B α → _) :=
  equivD.injective

/-- `toD` is injective. -/
@[simp]
theorem toD_inj {p q : SubInstrument A B α} : toD p = toD q ↔ p = q :=
  toD_injective.eq_iff

/-- `toD` sends `pure a` to `ret` at `a`. -/
@[simp]
theorem toD_pure (a : α) :
    toD (SubInstrument.pure a : SubInstrument A A α) = DSubInstrument.ret (fun _ ↦ A) a := by
  classical
  ext1
  rw [branch_toD, branch_pure, Finsupp.toDFinsupp_single, DSubInstrument.branch_ret]

/-- `toD` sends sequencing to sequencing. -/
theorem toD_bind (p : SubInstrument A B α) (k : α → SubInstrument B C β) :
    toD (p.bind k) = (toD p).bind fun a ↦ toD (k a) := by
  refine DSubInstrument.ext <| DFinsupp.ext fun c ↦ ?_
  rw [branch_toD_apply, branch_bind_apply, DSubInstrument.branch_bind_apply_of_forall_notMem
    (s := p.branch.support) _ _ fun a ha ↦ (Finsupp.notMem_support_iff.mp ha : p.branch a = 0)]
  rfl

/-- `toD` sends relabelling outcomes to reindexing outcomes. -/
theorem toD_map (f : α → β) (p : SubInstrument A B α) :
    toD (p.map f) = (toD p).map (C := fun _ ↦ B) f := by
  rw [map_eq_bind_pure, toD_bind]
  simp only [toD_pure]
  rfl

/-- `toD` sends failure to failure. -/
@[simp]
theorem toD_fail : toD (SubInstrument.fail : SubInstrument A B α) = DSubInstrument.fail :=
  DSubInstrument.ext <| DFinsupp.ext fun _ ↦ rfl

/-- `toD` commutes with framing by an ancilla. -/
@[simp]
theorem toD_frame (p : SubInstrument A B α) (R : Type*) [Fintype R] :
    toD (p.frame R) = (toD p).frame R :=
  DSubInstrument.ext <| DFinsupp.ext fun _ ↦ rfl

/-- `toD` sends a Kraus measurement to the Kraus measurement with constant output system. -/
@[simp]
theorem toD_ofKraus [Fintype α] [DecidableEq A] (K : α → Matrix B A ℂ)
    (hK : ∑ a, (K a)ᴴ * K a = 1) :
    toD (ofKraus K hK) = DSubInstrument.ofKraus (B := fun _ ↦ B) K hK :=
  DSubInstrument.ext <| DFinsupp.ext fun _ ↦ rfl

/-- `toD p` is lossless exactly when `p` is. -/
@[simp]
theorem lossless_toD_iff {p : SubInstrument A B α} : (toD p).Lossless ↔ p.Lossless :=
  (isTP_ltotal_iff p.branch).symm

end SubInstrument

end Quantum
