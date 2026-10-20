/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.ExceptT
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Events of exceptional computations

An exceptional computation is interpreted by core's lift of its base monad's expectation
interpretation (`ExpectationWP.exceptT`): `wp⟦mx⟧ g` is the expectation of `g` over the
successful results of the run, `wp⟦mx.run⟧ fun r => r.toOption.elim 0 g` (`wp_eq_run`), so an
exception contributes nothing. The measure interpretation of the stack agrees (`wp_ofMeasure_eq`),
which carries the laws of successful-output measures over.
-/

public section

open MeasureTheory Std.WP
open scoped ENNReal

universe v

namespace ExceptT

section lift

variable {m : Type → Type v} [Monad m] {EPred : Type} [Assertion EPred] [ExpectationWP m EPred]
  {ε α : Type}

/-- An expectation over an exceptional computation is the expectation over the successful
results of its run, with an exception worth `0`. -/
theorem wp_eq_run (mx : ExceptT ε m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = wp⟦mx.run⟧ fun r => r.toOption.elim 0 g := by
  rw [ExpectationWP.wp_liftExceptT_apply, ExpectationWP.bot_snd]
  refine ExpectationWP.wp_congr _ fun r => ?_
  cases r <;> simp [Lean.Order.pushExcept, Except.toOption]

/-- Successful events are the events of successful results in the underlying run. -/
theorem prEvent_eq_run (mx : ExceptT ε m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let r ← mx.run}[r.toOption.elim False p] := by
  rw [wp_eq_run]
  refine ExpectationWP.wp_congr _ fun r => ?_
  cases r <;> simp [Except.toOption]

/-- Throwing has every expectation `0`. -/
@[simp↓ high, grind norm↓]
theorem wp_throw (e : ε) (g : α → ℝ≥0∞) : wp⟦(throw e : ExceptT ε m α)⟧ g = 0 := by
  rw [wp_eq_run, ExceptT.run_throw, ExpectationWP.wp_pure]
  simp [Except.toOption]

/-- Lifting into the exceptional monad preserves every expectation. -/
@[simp high, grind norm↓]
theorem wp_lift (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦(ExceptT.lift mx : ExceptT ε m α)⟧ g = wp⟦mx⟧ g := by
  simp only [wp_eq_run, ExceptT.run_lift, ExpectationWP.wp_map, Except.toOption, Option.elim]

/-- Lifting into the exceptional monad preserves the probability of an observed event. -/
theorem prEvent_lift (mx : m α) (p : α → Prop) :
    Pr{let x ← (ExceptT.lift mx : ExceptT ε m α)}[p x] = Pr{let x ← mx}[p x] :=
  wp_lift mx _

/-- A monadic lift into the exceptional monad preserves every expectation. -/
@[simp high]
theorem wp_liftM (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦(liftM mx : ExceptT ε m α)⟧ g = wp⟦mx⟧ g :=
  wp_lift mx g

end lift

section measure

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {ε α : Type} [MeasurableSpace ε]

/-- The measure interpretation of an exceptional computation agrees with the lift: both
integrate the observation over the successful results. -/
@[simp, grind norm]
theorem wp_ofMeasure_eq (mx : ExceptT ε m α) (g : α → ℝ≥0∞) :
    @Std.WP.WP.wp _ _ ENNReal _ _ _ (@Std.WP.instWPOfWPMonad _ ENNReal _ _ _ _ _
      (ExpectationWP.toWPMonad (self := ExpectationWP.ofMeasure (ExceptT ε m)))) mx g
        Lean.Order.bot = wp⟦mx⟧ g := by
  let : MeasurableSpace α := ⊤
  have hobs : Measurable fun r : Except ε α => r.toOption.elim 0 g :=
    Except.measurable_elim measurable_const Measurable.of_discrete
  rw [wp_eq_run, ExpectationWP.wp_eq_lintegral (m := ExceptT ε m) mx g Measurable.of_discrete,
    ExceptT.evalDist_eq_comap_ok, Measure.comap_ok_eq_bind,
    Measure.lintegral_bind Measure.measurable_comap_ok_kernel.aemeasurable
      Measurable.of_discrete.aemeasurable,
    ExpectationWP.wp_eq_lintegral (m := m) mx.run _ hobs]
  refine lintegral_congr fun r => ?_
  cases r with
  | error e => simp [Except.toOption]
  | ok x => simp [Except.toOption, lintegral_dirac' x Measurable.of_discrete]

/-- Events of independent exceptional draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and {β : Type} (mx : ExceptT ε m α) (my : ExceptT ε m β)
    (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] = Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by
  simp only [← wp_ofMeasure_eq]
  exact _root_.prEvent_bind_bind_and mx my p q

/-- An event of two successive draws, which may read both outputs, integrates the event of the
second draw over a discrete first draw. -/
theorem prEvent_bind_bind_eq_lintegral_of_discrete {β : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (mx : ExceptT ε m α) (f : α → ExceptT ε m β) (p : α → β → Prop) :
    Pr{let x ← mx; let y ← f x}[p x y] = ∫⁻ x, Pr{let y ← f x}[p x y] ∂𝒟[mx] := by
  simp only [← wp_ofMeasure_eq]
  exact _root_.prEvent_bind_bind_eq_lintegral_of_discrete mx f p

/-- Two output maps of one computation: an event of the first map is at most an event of the
second when, at every output, the first event implies the second. -/
theorem prEvent_map_le_map {γ β : Type} (mx : ExceptT ε m γ) (f : γ → α) (g : γ → β)
    (p : α → Prop) (q : β → Prop) (h : ∀ x, p (f x) → q (g x)) :
    Pr{let y ← f <$> mx}[p y] ≤ Pr{let z ← g <$> mx}[q z] := by
  simp only [← wp_ofMeasure_eq]
  exact _root_.prEvent_map_le_map mx f g p q h

/-- An event of a pure computation is at most an event of another pure computation when the
first event implies the second. -/
theorem prEvent_pure_le_pure {β : Type} (a : α) (b : β) (p : α → Prop) (q : β → Prop)
    (h : p a → q b) :
    Pr{let y ← (pure a : ExceptT ε m α)}[p y] ≤ Pr{let z ← (pure b : ExceptT ε m β)}[q z] := by
  simp only [← wp_ofMeasure_eq]
  exact _root_.prEvent_pure_le_pure a b p q h

/-- The zero observation has expectation zero. -/
@[simp]
theorem wp_zero (mx : ExceptT ε m α) : wp⟦mx⟧ (fun _ => 0) = 0 := by
  rw [← wp_ofMeasure_eq]
  exact ExpectationWP.wp_zero mx

/-- A constant observation has the expectation of the constant times the success mass. -/
@[simp]
theorem wp_const (mx : ExceptT ε m α) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun _ => c) = c * Pr{let _ ← mx}[True] := by
  rw [← wp_ofMeasure_eq, ← wp_ofMeasure_eq]
  exact _root_.wp_const mx c

/-- An indicator observation scaled on the right is the scaled event. -/
@[simp]
theorem wp_propInd_mul (mx : ExceptT ε m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => propInd (p a) * c) = Pr{let x ← mx}[p x] * c := by
  rw [← wp_ofMeasure_eq, ← wp_ofMeasure_eq]
  exact _root_.wp_propInd_mul mx p c

/-- An indicator observation scaled on the left is the scaled event. -/
@[simp]
theorem wp_mul_propInd (mx : ExceptT ε m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => c * propInd (p a)) = c * Pr{let x ← mx}[p x] := by
  rw [← wp_ofMeasure_eq, ← wp_ofMeasure_eq]
  exact _root_.wp_mul_propInd mx p c

end measure

section sequencing

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {ε α β : Type} [MeasurableSpace ε]

/-- **An event of a draw bounds an event after its continuation.** An event `p` of `mx`, each of
whose possible occurrences leads almost surely to the event `q` of the continuation, has
probability at most that of `q` after the bind. -/
theorem prEvent_le_prEvent_bind_of_support (mx : ExceptT ε m α) (f : α → ExceptT ε m β)
    (p : α → Prop) (q : β → Prop) (h : ∀ a ∈ support mx, p a → Pr{let y ← f a}[q y] = 1) :
    Pr{let a ← mx}[p a] ≤ Pr{let y ← mx >>= f}[q y] := by
  simp only [← wp_ofMeasure_eq] at h ⊢
  exact _root_.prEvent_le_prEvent_bind_of_support mx f p q h

/-- A continuation event bounded by `δ` at the possible draws satisfying `p`, and null at the
possible draws outside `p`, is bounded after the draw by the probability of `p` times `δ`. -/
theorem prEvent_bind_le_prEvent_mul_of_forall_le_of_support (mx : ExceptT ε m α)
    (f : α → ExceptT ε m β) (p : α → Prop) (q : β → Prop) {δ : ℝ≥0∞}
    (h₁ : ∀ a ∈ support mx, p a → Pr{let y ← f a}[q y] ≤ δ)
    (h₂ : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] * δ := by
  simp only [← wp_ofMeasure_eq] at h₁ h₂ ⊢
  exact _root_.prEvent_bind_le_prEvent_mul_of_forall_le_of_support mx f p q h₁ h₂

end sequencing

end ExceptT
