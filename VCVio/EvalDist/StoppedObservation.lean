/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ResumptionCost
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# From finite observations to eventual return on a path space

A path model supplies measurable optional outputs, their finite truncation laws, and the
invariant that a returned value persists. These explicit obligations suffice to identify the
resumption's returned measure with the path event of eventually returning in a measurable set.
No measurable-space instance on arbitrary resumption syntax is assumed.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace PFunctor.Resumption

variable {P : PFunctor} [∀ a, MeasurableSpace (P.B a)] [P.AnswerMeasure]
  {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- Persistent finite observations identify every eventual-return event with the returned law. -/
theorem returnedMeasure_eq_observed_event [∀ a, DiscreteMeasurableSpace (P.B a)]
    (tree : Resumption P α) (μ : Measure Ω) (observe : ℕ → Ω → Option α)
    (hobserve : ∀ n, Measurable (observe n))
    (hpersist : ∀ ω n m a, n ≤ m → observe n ω = some a → observe m ω = some a)
    (hlaw : ∀ n, μ.map (observe n) = truncateMeasure n tree)
    (event : Set α) (hevent : MeasurableSet event) :
    returnedMeasure tree event = μ {ω | ∃ n, observe n ω ∈ some '' event} := by
  let events (n : ℕ) := observe n ⁻¹' (some '' event)
  have hmono : Monotone events := by
    intro n m hnm ω hω
    obtain ⟨a, ha, heq⟩ := hω
    exact ⟨a, ha, (hpersist ω n m a hnm heq.symm).symm⟩
  have hunion : {ω | ∃ n, observe n ω ∈ some '' event} = ⋃ n, events n := by
    ext ω; simp [events]
  rw [hunion, hmono.measure_iUnion, returnedMeasure_apply _ _ hevent]
  congr 1
  funext n
  rw [outputMeasure, Measure.dropNone_apply _ hevent, ← hlaw n,
    Measure.map_apply (hobserve n) (Option.measurableSet_some_image.mpr hevent)]

/-- The query-cost tail series is also the tail series in any finite-law-correct path model. -/
theorem expectedQueries_eq_observed_tails (tree : Resumption P α) (μ : Measure Ω)
    (observe : ℕ → Ω → Option α) (hobserve : ∀ n, Measurable (observe n))
    (hlaw : ∀ n, μ.map (observe n) = truncateMeasure n tree) :
    expectedQueries tree = ∑' n : ℕ, μ {ω | observe n ω = none} := by
  rw [expectedQueries_eq_tsum]
  congr 1
  funext n
  rw [← hlaw n, Measure.map_apply (hobserve n) Option.measurableSet_none]
  rfl

/-- Number of prefixes that have not yet returned, as an extended nonnegative path cost. -/
noncomputable def observedQueryCost (observe : ℕ → Ω → Option α) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, ({ω | observe n ω = none}).indicator (fun _ => 1) ω

/-- The tail-sum cost is the integral of the actual waiting-prefix count in a path realization. -/
theorem expectedQueries_eq_lintegral_observedCost (tree : Resumption P α) (μ : Measure Ω)
    (observe : ℕ → Ω → Option α) (hobserve : ∀ n, Measurable (observe n))
    (hlaw : ∀ n, μ.map (observe n) = truncateMeasure n tree) :
    expectedQueries tree = ∫⁻ ω, observedQueryCost observe ω ∂μ := by
  simp only [observedQueryCost]
  have hm (n : ℕ) : Measurable
      (({ω | observe n ω = none}).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator ((hobserve n) Option.measurableSet_none)
  rw [expectedQueries_eq_observed_tails tree μ observe hobserve hlaw,
    lintegral_tsum (fun n => (hm n).aemeasurable)]
  congr 1
  funext n
  exact (lintegral_indicator_one ((hobserve n) Option.measurableSet_none)).symm

end PFunctor.Resumption
