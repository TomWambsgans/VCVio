/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Runtime

/-!
# Simulation of runtimes

Two runtimes `R₁` and `R₂` for the same signature are related by a linear map
`V : MatrixMap R₁.D R₂.D` between the operators on their registers when every step of `R₂`
after `id ⊗ V` is `id ⊗ V` after the matching step of `R₁`:

`(R₂.step i).branch r ∘ₗ (id ⊗ V) = (id ⊗ V) ∘ₗ (R₁.step i).branch r`.

Then every program, run against `R₂` after `id ⊗ V`, is `id ⊗ V` after its run against `R₁`
(`Quantum.QuantumRuntime.simulation`). A program has no command on the runtime register, so
the proof is an induction on the program tree. The statement asks nothing of `V` beyond
linearity.

When `V` is trace preserving and sends the initial operator of `R₁` to that of `R₂`, no
observation by the program can tell the runtimes apart: the reduced post-states and the outcome
laws agree (`Quantum.QuantumRuntime.reducedPost_eq_of_simulation` and
`Quantum.QuantumRuntime.outcomeLaw_eq_of_simulation`). An example is a stateful runtime that
simulates a stateless one, such as a runtime that also counts the calls in its register (`V`
appends the counter) or a lazily sampled oracle against an eager one.

## Main definitions

* `Quantum.SubInstrument.Intertwines L₁ L₂ p p'`: on every outcome, `p'` after `L₁` is `L₂`
  after `p`.

## Main statements

* `Quantum.QuantumRuntime.simulation`.
* `Quantum.QuantumRuntime.reducedPost_eq_of_simulation`,
  `Quantum.QuantumRuntime.outcomeLaw_eq_of_simulation`.
-/

public section

open MeasureTheory
open scoped Kronecker

namespace Quantum

namespace SubInstrument

variable {X X' Y Y' Z Z' : Type*} [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y'] [Fintype Z]
  [Fintype Z'] {α β : Type*}

/-! ## Intertwining -/

/-- `p'` simulates `p` through `L₁` on inputs and `L₂` on outputs: on every outcome `a`,
`p'.branch a ∘ₗ L₁ = L₂ ∘ₗ p.branch a`. -/
@[expose]
def Intertwines (L₁ : MatrixMap X X') (L₂ : MatrixMap Y Y') (p : SubInstrument X Y α)
    (p' : SubInstrument X' Y' α) : Prop :=
  ∀ a, p'.branch a ∘ₗ L₁ = L₂ ∘ₗ p.branch a

/-- The branch of a composite as a sum over any finite set of outcomes containing the support of
the first subinstrument. -/
theorem branch_bind_apply_of_subset (p : SubInstrument X Y α) (k : α → SubInstrument Y Z β)
    {s : Finset α} (hs : p.branch.support ⊆ s) (b : β) :
    (p.bind k).branch b = ∑ a ∈ s, (k a).branch b ∘ₗ p.branch a := by
  rw [branch_bind_apply]
  exact Finset.sum_subset hs fun a _ ha ↦ by
    rw [Finsupp.notMem_support_iff.mp ha, LinearMap.comp_zero]

namespace Intertwines

/-- `pure a` intertwines with itself through any map. -/
theorem pure (L : MatrixMap X X') (a : α) :
    Intertwines L L (SubInstrument.pure a) (SubInstrument.pure a) := fun a' ↦ by
  classical
  simp only [branch_pure, Finsupp.single_apply]
  split_ifs
  · rw [LinearMap.id_comp, LinearMap.comp_id]
  · rw [LinearMap.zero_comp, LinearMap.comp_zero]

/-- Intertwining is preserved by sequencing. -/
theorem bind {L₁ : MatrixMap X X'} {L₂ : MatrixMap Y Y'} {L₃ : MatrixMap Z Z'}
    {p : SubInstrument X Y α} {p' : SubInstrument X' Y' α} {k : α → SubInstrument Y Z β}
    {k' : α → SubInstrument Y' Z' β} (hp : Intertwines L₁ L₂ p p')
    (hk : ∀ a, Intertwines L₂ L₃ (k a) (k' a)) :
    Intertwines L₁ L₃ (p.bind k) (p'.bind k') := fun b ↦ by
  classical
  rw [branch_bind_apply_of_subset p k (Finset.subset_union_left (s₂ := p'.branch.support)) b,
    branch_bind_apply_of_subset p' k' (Finset.subset_union_right (s₁ := p.branch.support)) b]
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have h₁ := LinearMap.congr_fun (hp a) ρ
  have h₂ := LinearMap.congr_fun (hk a b) (p.branch a ρ)
  simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
  rw [h₁, h₂]

/-- Framing by a common ancilla preserves intertwining. -/
theorem frame {L₁ : MatrixMap X X'} {L₂ : MatrixMap Y Y'} {p : SubInstrument X Y α}
    {p' : SubInstrument X' Y' α} (h : Intertwines L₁ L₂ p p') (E : Type*) [Fintype E] :
    Intertwines (L₁.amplify E) (L₂.amplify E) (p.frame E) (p'.frame E) := fun a ↦ by
  rw [branch_frame_apply, branch_frame_apply, ← MatrixMap.amplify_comp, h a,
    MatrixMap.amplify_comp]

/-- A subinstrument framed by two ancillas intertwines through a map `id ⊗ V` between the
ancillas. -/
theorem frame_amplifyLeft (p : SubInstrument X Y α) {R S : Type*} [Fintype R] [Fintype S]
    (V : MatrixMap R S) :
    Intertwines (V.amplifyLeft X) (V.amplifyLeft Y) (p.frame R) (p.frame S) := fun a ↦ by
  rw [branch_frame_apply, branch_frame_apply, MatrixMap.amplify_comp_amplifyLeft]

end Intertwines

end SubInstrument

namespace QuantumRuntime

open SubInstrument

variable {spec : QuantumOracleSpec} {A B : QReg} {α : Type}

section relabel

variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
  (V : MatrixMap R S)

/-- The relabelling before a call intertwines through `id ⊗ V` on both sides. -/
theorem intertwines_relabel_queryEquivIn {A I E : Type*} [Fintype A] [Fintype I] [Fintype E]
    [DecidableEq A] [DecidableEq I] [DecidableEq E] (ℓ : A ≃ I × E) :
    Intertwines (V.amplifyLeft A) ((V.amplifyLeft I).amplify E)
      (relabel (queryEquivIn ℓ R)) (relabel (queryEquivIn ℓ S)) := fun u ↦ by
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  simp only [LinearMap.comp_apply, relabel_branch_apply]
  rfl

/-- The relabelling after a call intertwines through `id ⊗ V` on both sides. -/
theorem intertwines_relabel_queryEquivOut (O E : Type*) [Fintype O] [Fintype E] [DecidableEq O]
    [DecidableEq E] :
    Intertwines ((V.amplifyLeft O).amplify E) (V.amplifyLeft (O × E))
      (relabel (queryEquivOut O R E)) (relabel (queryEquivOut O S E)) := fun u ↦ by
  refine LinearMap.ext fun ρ ↦ ?_
  ext x y
  simp only [LinearMap.comp_apply, relabel_branch_apply]
  rfl

end relabel

variable {R₁ R₂ : QuantumRuntime spec} {V : MatrixMap R₁.D R₂.D}

/-- A call intertwines through `id ⊗ V` when the port's steps do. -/
theorem intertwines_queryStep {i : spec.Port}
    (h : Intertwines (V.amplifyLeft (spec.In i)) (V.amplifyLeft (spec.Out i)) (R₁.step i)
      (R₂.step i))
    (E : QReg) (ℓ : A ≃ spec.In i × E) :
    Intertwines (V.amplifyLeft A) (V.amplifyLeft (QReg.of (spec.Out i × E)))
      (R₁.queryStep i E ℓ) (R₂.queryStep i E ℓ) :=
  (intertwines_relabel_queryEquivIn V ℓ).bind fun _ ↦ (h.frame E).bind fun r ↦
    (intertwines_relabel_queryEquivOut V (spec.Out i) E).bind fun _ ↦ Intertwines.pure _ r

/-- **Simulation.** If every step of `R₂` after `id ⊗ V` is `id ⊗ V` after the matching step of
`R₁`, then every program run against `R₂` after `id ⊗ V` is `id ⊗ V` after its run against
`R₁`, on every outcome. -/
theorem simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (x : QuantumComp spec A B α) (a : α) :
    (R₂.run x).branch a ∘ₗ V.amplifyLeft A = V.amplifyLeft B ∘ₗ (R₁.run x).branch a := by
  revert a
  refine QuantumComp.inductionOn (motive := fun A B x ↦
    Intertwines (V.amplifyLeft A) (V.amplifyLeft B) (R₁.run x) (R₂.run x)) ?_ ?_ ?_ x
  · exact fun _ a ↦ Intertwines.pure _ a
  · intro _ _ _ _ p k ih
    rw [run_act_bind, run_act_bind]
    exact (Intertwines.frame_amplifyLeft p V).bind ih
  · intro _ _ i E ℓ k ih
    rw [run_query_bind, run_query_bind]
    exact (intertwines_queryStep (h i) E ℓ).bind ih

/-- Under a simulation, the joint post-state against `R₂` is `id ⊗ V` of the joint post-state
against `R₁`, when `V` sends the initial operator of `R₁` to that of `R₂`. -/
theorem matrix_jointPost_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp spec A B α) (ρ : SubState A)
    (a : α) :
    (R₂.jointPost x ρ a).matrix = V.amplifyLeft B (R₁.jointPost x ρ a).matrix := by
  rw [matrix_jointPost, matrix_jointPost, ← hinit, ← MatrixMap.amplifyLeft_kronecker,
    ← LinearMap.comp_apply, simulation h x a, LinearMap.comp_apply]

/-- **Indistinguishability.** Under a simulation through a trace-preserving `V` that sends the
initial operator of `R₁` to that of `R₂`, the reduced post-states of every program agree. -/
theorem reducedPost_eq_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp spec A B α)
    (ρ : SubState A) (a : α) : R₂.reducedPost x ρ a = R₁.reducedPost x ρ a :=
  SubState.ext <| by
    rw [reducedPost, reducedPost, SubState.matrix_traceRight, SubState.matrix_traceRight,
      matrix_jointPost_of_simulation h hinit x ρ a, ← LinearMap.comp_apply,
      MatrixMap.traceRight_comp_amplifyLeft hV]

/-- Under the hypotheses of `reducedPost_eq_of_simulation`, the joint post-states of every
program have the same trace. -/
theorem trace_jointPost_eq_of_simulation
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp spec A B α)
    (ρ : SubState A) (a : α) :
    (R₂.jointPost x ρ a).matrix.trace = (R₁.jointPost x ρ a).matrix.trace := by
  rw [← trace_reducedPost, ← trace_reducedPost, reducedPost_eq_of_simulation h hV hinit]

/-- **Indistinguishability.** Under a simulation through a trace-preserving `V` that sends the
initial operator of `R₁` to that of `R₂`, the outcome laws of every program agree. -/
theorem outcomeLaw_eq_of_simulation [MeasurableSpace α]
    (h : ∀ i r, (R₂.step i).branch r ∘ₗ V.amplifyLeft (spec.In i) =
      V.amplifyLeft (spec.Out i) ∘ₗ (R₁.step i).branch r)
    (hV : V.IsTP) (hinit : V R₁.init.matrix = R₂.init.matrix) (x : QuantumComp spec A B α)
    (ρ : SubState A) : R₂.outcomeLaw x ρ = R₁.outcomeLaw x ρ := by
  classical
  rw [outcomeLaw, outcomeLaw,
    outcomeMeasure_eq_sum_of_subset _ _ (Finset.subset_union_left
      (s₂ := (R₁.run x).branch.support)),
    outcomeMeasure_eq_sum_of_subset _ _ (Finset.subset_union_right
      (s₁ := (R₂.run x).branch.support))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have := trace_jointPost_eq_of_simulation h hV hinit x ρ a
  rw [matrix_jointPost, matrix_jointPost] at this
  rw [SubState.matrix_prod, SubState.matrix_prod, this]

end QuantumRuntime

end Quantum
