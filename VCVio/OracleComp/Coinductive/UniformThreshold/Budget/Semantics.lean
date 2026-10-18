/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Budget
public import VCVio.EvalDist.KernelHandler.Except
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.MachinePath
public import ToMathlib.MeasureTheory.MeasurableSpace.NNRat

/-!
# Joint laws of admitted threshold clients

The service kernel retains the explicit error or Boolean answer together with
the updated dyadic prefix and rational allowance. Its law extends to every
adaptive finite client through the common exception-answer adapter. Refusal and
timeout are ordinary probability outcomes; neither discards the retained state.
-/

public section

open OracleComp PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UniformThreshold.Budget

instance : MeasurableSpace Failure := ⊤

instance : DiscreteMeasurableSpace Failure := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable Failure := Function.Injective.countable
  (f := fun x : Failure => match x with | .budgetExhausted => false | .timeout => true) (by
    intro x y h
    cases x <;> cases y <;> simp_all)

/-- The joint error-or-answer and retained-state law of an admitted operation. -/
noncomputable def answerKernel (cap : ℚ → Session → ℕ) :
    KernelHandler (spec.toPFunctor.withExcept Failure) Session := fun q =>
  ⟨fun state => 𝒟[((handler cap q).run).run state], Measurable.of_discrete⟩

/-- Each capped operation terminates with either an answer or an explicit error. -/
instance (cap : ℚ → Session → ℕ) (q : ℚ) : IsMarkovKernel (answerKernel cap q) := by
  refine ⟨fun state => ?_⟩
  change IsProbabilityMeasure 𝒟[((handler cap q).run).run state]
  exact FreeM.isProbabilityMeasure_denote _

/-- The executable service realizes its explicit exceptional-answer kernel. -/
theorem realizes (cap : ℚ → Session → ℕ) :
    (answerKernel cap).Realizes (handler cap).exceptAnswers := fun _ _ => rfl

/-- The finite client's full law includes the failure tag, sampled prefix and unused allowance. -/
theorem evalDist_run {α : Type} [MeasurableSpace α] (cap : ℚ → Session → ℕ)
    (program : FreeM spec.toPFunctor α) (state : Session) :
    𝒟[run cap program state] = FreeM.runKernel (answerKernel cap) program.withExcept state :=
  (realizes cap).runExcept program state

/-- Refusal produces a point mass at the original state, including the untouched allowance. -/
theorem answerKernel_of_refused (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : state.2 < charge (cap q state)) :
    answerKernel cap q state = Measure.dirac (.error .budgetExhausted, state) := by
  change 𝒟[((handler cap q).run).run state] = _
  rw [show ((handler cap q).run).run state = pure (.error .budgetExhausted, state) from
    machineHandler.admitted_run_error (admission cap) _ q state .budgetExhausted
      (admission_error cap q state h)]
  exact evalDist_pure _

/-- Observe only a successful value and prefix, forgetting the allowance and all errors. -/
@[expose] def successfulResult {α : Type} (out : Except Failure α × Session) :
    Option (α × Prefix) := out.1.toOption.map (fun value => (value, out.2.1))

/-- After admission, forgetting errors and budget recovers the capped threshold law. -/
theorem map_answerKernel_of_admitted (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    (answerKernel cap q state).map successfulResult = boundedLaw q state.1 (cap q state) := by
  change (𝒟[((handler cap q).run).run state]).map successfulResult = _
  rw [show ((handler cap q).run).run state =
    FreeM.map (machineHandler.finishAdmitted (fun _ _ residual => (.timeout, residual)) q
      (state.1, state.2 - charge (cap q state)))
      ((machine q).unrollChunk (cap q state) state.1) from
        machineHandler.admitted_run_ok (admission cap) _ q state _ _
          (admission_ok cap q state h)]
  change (FreeM.denote (P := coinSpec.toPFunctor) (FreeM.map _ _)).map successfulResult = _
  rw [← FreeM.denote_map_of_measurable (P := coinSpec.toPFunctor)
      _ successfulResult Measurable.of_discrete,
    FreeM.map_map]
  have hproj : successfulResult ∘
      machineHandler.finishAdmitted (fun _ _ residual => (.timeout, residual)) q
        (state.1, state.2 - charge (cap q state)) = DynSystem.DynComputation.Chunk.result := by
    funext chunk
    cases chunk <;> rfl
  rw [hproj, DynSystem.DynComputation.unrollChunk_result]
  rw [boundedLaw_eq_truncateMeasure]
  exact DynSystem.DynComputation.denote_unroll _ _ _

/-- The actual error-and-state kernel charges at most the reserved allowance after admission. -/
theorem failure_le_charge_of_admitted (cap : ℚ → Session → ℕ) (q : ℚ) (state : Session)
    (h : charge (cap q state) ≤ state.2) :
    answerKernel cap q state {out | out.1.toOption = none} ≤ (charge (cap q state) : ℝ≥0∞) := by
  have hcutoff := cutoff_le_charge q state.1 (cap q state)
  rw [← map_answerKernel_of_admitted cap q state h,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton none)] at hcutoff
  have hevent : (successfulResult ⁻¹' {none} : Set (Except Failure Bool × Session)) =
      {out | out.1.toOption = none} := by
    ext out
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      successfulResult, Option.map_eq_none_iff]
  rwa [hevent] at hcutoff

end UniformThreshold.Budget
