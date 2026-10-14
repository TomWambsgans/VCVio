/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Runtime

/-!
# Query budgets of quantum programs

A program `x` has query budget `b : spec.Port → ℕ` when, along every path of its tree and on
every branch, it calls each port `i` at most `b i` times. The budget is a property of the tree,
not a type index: the number of calls may depend on classical outcomes, and only its worst case
over paths is bounded.

Paths include branches that are reached with weight zero, so a budget is a syntactic bound, and
it holds against every runtime.

## Implementation note

PolyFun's `PFunctor.FreeM.IsRollBound` bounds the commands of the non-indexed free monad
`PFunctor.FreeM`. Programs are trees of the indexed free monad `IPFunctor.FreeM₂`, so
`IsRollBound` does not apply directly; transporting through `IFreeM.toSigmaFreeM` would carry
the equality witnesses of the leaves through every statement. The bound is therefore defined by
recursion on the tree, one port at a time (`Quantum.QuantumComp.IsQueryBoundAt`). Counting one
port at a time needs no decidable equality on ports.

## Main definitions

* `Quantum.QuantumComp.IsQueryBoundAt i x n`: every path of `x` calls port `i` at most `n`
  times.
* `Quantum.QuantumComp.IsQueryBound x b`: every path of `x` calls each port `i` at most `b i`
  times.

## Main statements

* `IsQueryBound.mono`, `isQueryBound_pure`, `isQueryBound_act`, `isQueryBound_query_iff` and
  `IsQueryBound.bind` (budgets add under sequencing).
* `Quantum.QuantumRuntime.run_congr_of_isQueryBound`: two runtimes on the same register whose
  steps agree on every port with a nonzero budget run a program within that budget to the same
  subinstrument.
-/

public section

open IPFunctor

namespace Quantum

namespace QuantumComp

variable {spec : QuantumOracleSpec} {A B C : QReg} {α β γ : Type}

/-! ## Budgets on one port -/

/-- Every path of the tree calls port `i` at most `n` times. -/
@[expose]
def isQueryBoundAtAux (i : spec.Port) {B : QReg} :
    {A : QReg} → IFreeM spec.toIPFunctor (fun u ↦ PSigma fun _ : u = B ↦ α) A → ℕ → Prop
  | _, .pure _, _ => True
  | _, .liftBind (.act _ _ _) k, n => ∀ b, isQueryBoundAtAux i (k b) n
  | _, .liftBind (.query j _ _) k, n =>
      (j = i → 0 < n ∧ ∀ r, isQueryBoundAtAux i (k r) (n - 1)) ∧
        (j ≠ i → ∀ r, isQueryBoundAtAux i (k r) n)

/-- Every path of `x`, including paths reached with weight zero, calls port `i` at most `n`
times. -/
@[expose]
def IsQueryBoundAt (x : QuantumComp spec A B α) (i : spec.Port) (n : ℕ) : Prop :=
  isQueryBoundAtAux i x n

/-- A program that returns at once makes no call. -/
@[simp]
theorem isQueryBoundAt_pure (a : α) (i : spec.Port) (n : ℕ) :
    (QuantumComp.pure a : QuantumComp spec A A α).IsQueryBoundAt i n :=
  trivial

/-- A local subinstrument followed by a continuation is bounded when every continuation is. -/
@[simp]
theorem isQueryBoundAt_act_bind_iff (p : SubInstrument A B β) (k : β → QuantumComp spec B C α)
    (i : spec.Port) (n : ℕ) :
    ((act p).bind k).IsQueryBoundAt i n ↔ ∀ b, (k b).IsQueryBoundAt i n :=
  Iff.rfl

/-- A call of port `j` followed by a continuation: if `j = i` it uses one unit of the budget,
and the continuations must fit in the rest. -/
theorem isQueryBoundAt_query_bind_iff (j : spec.Port) (E : QReg) (ℓ : A ≃ spec.In j × E)
    (k : spec.Result j → QuantumComp spec (QReg.of (spec.Out j × E)) C α) (i : spec.Port)
    (n : ℕ) :
    ((query j E ℓ).bind k).IsQueryBoundAt i n ↔
      (j = i → 0 < n ∧ ∀ r, (k r).IsQueryBoundAt i (n - 1)) ∧
        (j ≠ i → ∀ r, (k r).IsQueryBoundAt i n) :=
  Iff.rfl

/-- A budget on one port can be enlarged. -/
theorem IsQueryBoundAt.mono {x : QuantumComp spec A B α} {i : spec.Port} {n m : ℕ}
    (hx : x.IsQueryBoundAt i n) (hnm : n ≤ m) : x.IsQueryBoundAt i m := by
  refine QuantumComp.inductionOn (motive := fun A B x ↦ ∀ {n m : ℕ},
    x.IsQueryBoundAt i n → n ≤ m → x.IsQueryBoundAt i m) ?_ ?_ ?_ x hx hnm
  · exact fun _ a _ _ _ _ ↦ trivial
  · intro _ _ _ _ p k ih n m hx hnm
    exact fun b ↦ ih b (hx b) hnm
  · intro _ _ j E ℓ k ih n m hx hnm
    rw [isQueryBoundAt_query_bind_iff] at hx ⊢
    exact ⟨fun hj ↦ ⟨lt_of_lt_of_le (hx.1 hj).1 hnm, fun r ↦ ih r ((hx.1 hj).2 r)
      (Nat.sub_le_sub_right hnm 1)⟩, fun hj r ↦ ih r (hx.2 hj r) hnm⟩

/-- Budgets on one port add under sequencing. -/
theorem IsQueryBoundAt.bind {x : QuantumComp spec A B α} {k : α → QuantumComp spec B C β}
    {i : spec.Port} {n m : ℕ} (hx : x.IsQueryBoundAt i n) (hk : ∀ a, (k a).IsQueryBoundAt i m) :
    (x.bind k).IsQueryBoundAt i (n + m) := by
  refine QuantumComp.inductionOn (motive := fun A B x ↦ ∀ {C : QReg}
    (k : α → QuantumComp spec B C β) {n : ℕ}, x.IsQueryBoundAt i n →
      (∀ a, (k a).IsQueryBoundAt i m) → (x.bind k).IsQueryBoundAt i (n + m)) ?_ ?_ ?_ x k hx hk
  · exact fun _ a _ k n _ hk ↦ (hk a).mono (Nat.le_add_left m n)
  · intro _ _ _ _ p k' ih _ k n hx hk
    rw [QuantumComp.bind_assoc, isQueryBoundAt_act_bind_iff]
    exact fun b ↦ ih b k (hx b) hk
  · intro _ _ j E ℓ k' ih _ k n hx hk
    rw [isQueryBoundAt_query_bind_iff] at hx
    rw [QuantumComp.bind_assoc, isQueryBoundAt_query_bind_iff]
    refine ⟨fun hj ↦ ⟨Nat.add_pos_left (hx.1 hj).1 m, fun r ↦ ?_⟩,
      fun hj r ↦ ih r k (hx.2 hj r) hk⟩
    rw [Nat.sub_add_comm (hx.1 hj).1]
    exact ih r k ((hx.1 hj).2 r) hk

/-! ## Budgets on all ports -/

/-- **Query budget.** Every path of `x`, including paths reached with weight zero, calls each
port `i` at most `b i` times. -/
@[expose]
def IsQueryBound (x : QuantumComp spec A B α) (b : spec.Port → ℕ) : Prop :=
  ∀ i, x.IsQueryBoundAt i (b i)

/-- A budget can be enlarged. -/
theorem IsQueryBound.mono {x : QuantumComp spec A B α} {b b' : spec.Port → ℕ}
    (hx : x.IsQueryBound b) (hb : b ≤ b') : x.IsQueryBound b' :=
  fun i ↦ (hx i).mono (hb i)

/-- A program that returns at once has every budget. -/
@[simp]
theorem isQueryBound_pure (a : α) (b : spec.Port → ℕ) :
    (QuantumComp.pure a : QuantumComp spec A A α).IsQueryBound b :=
  fun _ ↦ trivial

/-- A local subinstrument has every budget. -/
@[simp]
theorem isQueryBound_act (p : SubInstrument A B α) (b : spec.Port → ℕ) :
    (act (spec := spec) p).IsQueryBound b :=
  fun _ _ ↦ trivial

/-- A local subinstrument followed by a continuation is within a budget when every
continuation is. -/
@[simp]
theorem isQueryBound_act_bind_iff (p : SubInstrument A B β) (k : β → QuantumComp spec B C α)
    (b : spec.Port → ℕ) : ((act p).bind k).IsQueryBound b ↔ ∀ c, (k c).IsQueryBound b :=
  forall_comm

/-- A single call of port `i` is within a budget exactly when the budget of `i` is nonzero. -/
@[simp]
theorem isQueryBound_query_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (b : spec.Port → ℕ) : (query i E ℓ).IsQueryBound b ↔ 0 < b i :=
  ⟨fun h ↦ ((h i).1 rfl).1, fun h _ ↦
    ⟨fun hij ↦ ⟨hij ▸ h, fun _ ↦ trivial⟩, fun _ _ ↦ trivial⟩⟩

/-- Budgets add under sequencing. -/
theorem IsQueryBound.bind {x : QuantumComp spec A B α} {k : α → QuantumComp spec B C β}
    {b₁ b₂ : spec.Port → ℕ} (hx : x.IsQueryBound b₁) (hk : ∀ a, (k a).IsQueryBound b₂) :
    (x.bind k).IsQueryBound (b₁ + b₂) :=
  fun i ↦ (hx i).bind fun a ↦ hk a i

/-- A call of port `i` followed by continuations within a budget `b` uses part of the budget of
`i`: the budget of `i` is nonzero, and the continuations are within `b`. -/
theorem IsQueryBound.of_query_bind {i : spec.Port} {E : QReg} {ℓ : A ≃ spec.In i × E}
    {k : spec.Result i → QuantumComp spec (QReg.of (spec.Out i × E)) C α} {b : spec.Port → ℕ}
    (h : ((query i E ℓ).bind k).IsQueryBound b) : 0 < b i ∧ ∀ r, (k r).IsQueryBound b := by
  have h' := fun j ↦ (isQueryBoundAt_query_bind_iff i E ℓ k j (b j)).mp (h j)
  refine ⟨((h' i).1 rfl).1, fun r j ↦ ?_⟩
  by_cases hij : i = j
  · subst hij
    exact (((h' i).1 rfl).2 r).mono (Nat.sub_le _ 1)
  · exact (h' j).2 hij r

/-- A call of port `i` followed by continuations is within the budget `b` exactly when the
budget of `i` is nonzero and the continuations are within `b` with one call of `i` spent. -/
theorem isQueryBound_query_bind_iff [DecidableEq spec.Port] (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp spec (QReg.of (spec.Out i × E)) C α) (b : spec.Port → ℕ) :
    ((query i E ℓ).bind k).IsQueryBound b ↔
      0 < b i ∧ ∀ r, (k r).IsQueryBound (Function.update b i (b i - 1)) := by
  constructor
  · intro h
    have h' := fun j ↦ (isQueryBoundAt_query_bind_iff i E ℓ k j (b j)).mp (h j)
    refine ⟨((h' i).1 rfl).1, fun r j ↦ ?_⟩
    by_cases hij : j = i
    · subst hij
      rw [Function.update_self]
      exact ((h' j).1 rfl).2 r
    · rw [Function.update_of_ne hij]
      exact (h' j).2 (Ne.symm hij) r
  · rintro ⟨hb, hk⟩ j
    refine (isQueryBoundAt_query_bind_iff i E ℓ k j (b j)).mpr ⟨fun hij ↦ ?_, fun hij r ↦ ?_⟩
    · subst hij
      exact ⟨hb, fun r ↦ by simpa using hk r i⟩
    · simpa [Function.update_of_ne (Ne.symm hij)] using hk r j

end QuantumComp

namespace QuantumRuntime

variable {spec : QuantumOracleSpec} {A B : QReg} {α : Type}

/-- **Unused ports do not matter.** Two runtimes on the same register whose steps agree on every
port with a nonzero budget run every program within that budget to the same subinstrument. The
initial substates may differ: `run` does not read them. -/
theorem run_congr_of_isQueryBound {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {x : QuantumComp spec A B α} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hs : ∀ i, b i ≠ 0 → s₁ i = s₂ i) :
    (QuantumRuntime.mk D σ₁ s₁).run x = (QuantumRuntime.mk D σ₂ s₂).run x := by
  refine QuantumComp.inductionOn (motive := fun A B x ↦ x.IsQueryBound b →
    (QuantumRuntime.mk D σ₁ s₁).run x = (QuantumRuntime.mk D σ₂ s₂).run x) ?_ ?_ ?_ x hx
  · exact fun _ a _ ↦ rfl
  · intro _ _ _ _ p k ih hx
    rw [QuantumComp.isQueryBound_act_bind_iff] at hx
    rw [run_act_bind, run_act_bind]
    exact congrArg _ (funext fun c ↦ ih c (hx c))
  · intro _ _ i E ℓ k ih hx
    obtain ⟨hb, hk⟩ := hx.of_query_bind
    rw [run_query_bind, run_query_bind]
    have hstep : (QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ =
        (QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ := by
      simp only [queryStep, hs i hb.ne']
    rw [hstep]
    exact congrArg _ (funext fun r ↦ ih r (hk r))

end QuantumRuntime

end Quantum
