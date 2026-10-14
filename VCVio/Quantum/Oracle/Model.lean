/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.Quantum.Oracle.Adversary
public import VCVio.Quantum.Oracle.Unitary

/-!
# The quantum random-oracle model

An oracle is realized on the register of a query adversary by a family of query steps indexed by a
sampled value. `Quantum.QueryAdversary.outcomeLaw` draws the value uniformly, with VCVio's `$ᵗ`,
and observes the run of the adversary against the corresponding query step. The quantum
random-oracle model is the instance in which the sampled value is a function `H : X → Y` and the
query step is its oracle unitary (`Quantum.QueryAdversary.qromLaw`). Another realization of the
oracle is another family of query steps for the same adversary, and "same outcome law" is an
equation between two values of `Quantum.QueryAdversary.outcomeLaw`.

Events that mention the sampled value, such as "the adversary's guess `(x, y)` satisfies
`y = H x`", are measured by `Quantum.QueryAdversary.outcomeLawWith`, which relabels the output of
each run by a function that sees the sampled value.

## Main results

* `Quantum.QueryAdversary.qromLaw_eq_sum`: the law is the average over all functions of the
  outcome measures of the runs.
* `Quantum.QueryAdversary.qromLawWith_guess_zero`: without queries, a guess `(x, y)` satisfies
  `y = H x` with probability the trace of the initial substate divided by `|Y|`; from a normalized
  initial state this is `1 / |Y|` (`Quantum.QueryAdversary.qromLawWith_guess_zero_of_trace_eq_one`).
* `Quantum.QueryAdversary.outcomeMeasure_run_oracleQuery_eq_of_eqOn`: if every query acts on a
  substate supported on the query inputs in `S`, the outcome measure only depends on the
  restriction of the function to `S`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

namespace Quantum

namespace QueryAdversary

variable {M : Type*} [Fintype M] {α β : Type*} {q : ℕ}

/-! ## Outcome laws against a sampled oracle -/

section outcomeLaw

variable {Ω : Type} [SampleableType Ω]

/-- The law of the output of `adv`, relabelled by a function that sees the sampled value, when
`ω` is drawn uniformly and the oracle is realized by the query step `oracle ω`: the mixture over
`ω` of the outcome measures of `f ω <$> adv.run (oracle ω)` on the initial substate. -/
@[expose]
noncomputable def outcomeLawWith [MeasurableSpace β] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) (f : Ω → α → β) : Measure β :=
  letI : MeasurableSpace Ω := ⊤
  (𝒟[$ᵗ Ω]).bind fun ω ↦ ((adv.run (oracle ω)).map (f ω)).outcomeMeasure adv.init

/-- The law of the output of `adv` when `ω` is drawn uniformly and the oracle is realized by the
query step `oracle ω`: the mixture over `ω` of the outcome measures of the runs on the initial
substate. -/
@[expose]
noncomputable def outcomeLaw [MeasurableSpace α] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) : Measure α :=
  letI : MeasurableSpace Ω := ⊤
  (𝒟[$ᵗ Ω]).bind fun ω ↦ (adv.run (oracle ω)).outcomeMeasure adv.init

/-- Relabelling the output without looking at the sampled value or changing the output gives the
outcome law. -/
theorem outcomeLawWith_id [MeasurableSpace α] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) :
    adv.outcomeLawWith oracle (fun _ a ↦ a) = adv.outcomeLaw oracle := by
  simp only [outcomeLawWith, outcomeLaw]
  congr 1
  funext ω
  rw [show (fun a : α ↦ a) = id from rfl, SubInstrument.map_id]

section fintype

variable [Fintype Ω]

/-- The relabelled outcome law of a measurable set averages, over the sampled values, its
measure under the relabelled runs. -/
theorem outcomeLawWith_apply [MeasurableSpace β] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) (f : Ω → α → β) {s : Set β} (hs : MeasurableSet s) :
    adv.outcomeLawWith oracle f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ *
        ((adv.run (oracle ω)).map (f ω)).outcomeMeasure adv.init s := by
  let : MeasurableSpace Ω := ⊤
  rw [outcomeLawWith, SampleableType.evalDist_uniformSample, uniformOn_univ_bind_apply _ _ hs]

/-- The relabelled outcome law is the average, over the sampled values, of the outcome measures
of the relabelled runs. -/
theorem outcomeLawWith_eq_sum [MeasurableSpace β] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) (f : Ω → α → β) :
    adv.outcomeLawWith oracle f =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ •
        ∑ ω, ((adv.run (oracle ω)).map (f ω)).outcomeMeasure adv.init := by
  refine Measure.ext fun s hs ↦ ?_
  rw [outcomeLawWith_apply _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

/-- The outcome law of a measurable set averages, over the sampled values, its measure under
the runs. -/
theorem outcomeLaw_apply [MeasurableSpace α] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) {s : Set α} (hs : MeasurableSet s) :
    adv.outcomeLaw oracle s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (adv.run (oracle ω)).outcomeMeasure adv.init s := by
  let : MeasurableSpace Ω := ⊤
  rw [outcomeLaw, SampleableType.evalDist_uniformSample, uniformOn_univ_bind_apply _ _ hs]

/-- The outcome law is the average, over the sampled values, of the outcome measures of the
runs. -/
theorem outcomeLaw_eq_sum [MeasurableSpace α] (adv : QueryAdversary M α q)
    (oracle : Ω → SubInstrument M M Unit) :
    adv.outcomeLaw oracle =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (adv.run (oracle ω)).outcomeMeasure adv.init := by
  refine Measure.ext fun s hs ↦ ?_
  rw [outcomeLaw_apply _ _ hs, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

end fintype

/-- Against lossless query steps, the outcome law has total mass the trace of the initial
substate. -/
theorem outcomeLaw_apply_univ [MeasurableSpace α] (adv : QueryAdversary M α q)
    {oracle : Ω → SubInstrument M M Unit} (h : ∀ ω, (oracle ω).Lossless) :
    adv.outcomeLaw oracle Set.univ = ENNReal.ofReal adv.init.matrix.trace.re := by
  let : Fintype Ω := Fintype.ofFinite Ω
  rw [outcomeLaw_apply _ _ MeasurableSet.univ]
  simp only [adv.outcomeMeasure_run_apply_univ (h _)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

end outcomeLaw

/-! ## Guessing a value of a uniform function -/

section guess

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y]

/-- Each value is taken at a given input by the same number of functions: the functions with
`H x = y`, times `|Y|`, are all the functions. -/
theorem card_filter_apply_eq_mul_card [DecidableEq Y] (x : X) (y : Y) :
    (Finset.univ.filter fun H : X → Y ↦ H x = y).card * Fintype.card Y =
      Fintype.card (X → Y) := by
  have hfib : ∀ y' : Y, (Finset.univ.filter fun H : X → Y ↦ H x = y').card =
      (Finset.univ.filter fun H : X → Y ↦ H x = y).card := fun y' ↦
    Finset.card_equiv (Equiv.addRight fun _ ↦ y - y') fun H ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ (congrArg (· + (y - y')) h).trans (add_sub_cancel y' y),
        fun h ↦ add_right_cancel (h.trans (add_sub_cancel y' y).symm)⟩
  have h := Finset.card_eq_sum_card_fiberwise (f := fun H : X → Y ↦ H x) (s := Finset.univ)
    (t := Finset.univ) fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl fun b _ ↦ hfib b, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm]

/-- A guess that does not depend on the function is right with probability the total weight
divided by `|Y|`: for a quantum computation `P` on a substate `ρ`, averaging over all functions
`H` the weight with which the output `a` of `P` satisfies `y a = H (x a)` gives the trace of the
total output of `P` on `ρ` divided by `|Y|`. For a lossless `P` this is the trace of `ρ` divided
by `|Y|` (`Quantum.QueryAdversary.qromLawWith_guess_zero`), and `1 / |Y|` when `ρ` is normalized
(`Quantum.QueryAdversary.qromLawWith_guess_zero_of_trace_eq_one`). -/
theorem sum_outcomeMeasure_map_guess {M : Type*} [Fintype M] (P : SubInstrument M M α)
    (ρ : SubState M) (x : α → X) (y : α → Y) :
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        (P.map fun a ↦ y a = H (x a)).outcomeMeasure ρ {True} =
      ENNReal.ofReal (P.total ρ.matrix).trace.re / Fintype.card Y := by
  classical
  have hcount : ∀ a : α, ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
      (if y a = H (x a) then 1 else 0) = (Fintype.card Y : ℝ≥0∞)⁻¹ := fun a ↦ by
    have hc := card_filter_apply_eq_mul_card (x a) (y a)
    have hfilter : (Finset.univ.filter fun H : X → Y ↦ y a = H (x a)) =
        Finset.univ.filter fun H : X → Y ↦ H (x a) = y a :=
      Finset.filter_congr fun _ _ ↦ eq_comm
    have hne : ((Finset.univ.filter fun H : X → Y ↦ H (x a) = y a).card : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun h0 ↦
        (Fintype.card_pos (α := X → Y)).ne' (by rw [← hc, h0, zero_mul])
    rw [← Finset.mul_sum, Finset.sum_boole, hfilter, ← hc, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl hne) (Or.inl (ENNReal.natCast_ne_top _)), mul_right_comm,
      ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul]
  have hterm : ∀ a ∈ P.branch.support, ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal (P.branch a ρ.matrix).trace.re *
        Set.indicator {True} 1 (y a = H (x a))) =
      ENNReal.ofReal (P.branch a ρ.matrix).trace.re * (Fintype.card Y : ℝ≥0∞)⁻¹ :=
    fun a _ ↦ by
      rw [← hcount a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun H _ ↦ ?_
      rw [mul_left_comm]
      congr 2
      by_cases h : y a = H (x a) <;> simp [h]
  simp only [SubInstrument.outcomeMeasure_map, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.singleton True), smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl hterm, ← Finset.sum_mul, div_eq_mul_inv,
    SubInstrument.total_eq_sum, LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦ P.trace_re_branch_apply_nonneg a ρ.posSemidef]

end guess

/-! ## The quantum random-oracle model -/

section qrom

variable {X Y W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype W] [DecidableEq W]

section sampled

variable [SampleableType (X → Y)]

/-- The law of the output of `adv` in the quantum random-oracle model, relabelled by a function
that sees the random function: `H : X → Y` is drawn uniformly, the adversary runs against the
oracle unitary of `H`, and its output `a` is reported as `f H a`. -/
@[expose]
noncomputable def qromLawWith [MeasurableSpace β] (adv : QueryAdversary (X × Y × W) α q)
    (f : (X → Y) → α → β) : Measure β :=
  adv.outcomeLawWith oracleQuery f

/-- The law of the output of `adv` in the quantum random-oracle model: `H : X → Y` is drawn
uniformly and the adversary runs against the oracle unitary of `H`. -/
@[expose]
noncomputable def qromLaw [MeasurableSpace α] (adv : QueryAdversary (X × Y × W) α q) :
    Measure α :=
  adv.outcomeLaw oracleQuery

/-- Relabelling the output without looking at the random function or changing the output gives
the law of the quantum random-oracle model. -/
theorem qromLawWith_id [MeasurableSpace α] (adv : QueryAdversary (X × Y × W) α q) :
    adv.qromLawWith (fun _ a ↦ a) = adv.qromLaw :=
  adv.outcomeLawWith_id _

/-- The law of the quantum random-oracle model is the average, over all `|Y| ^ |X|` functions,
of the outcome measures of the runs against their oracle unitaries. -/
theorem qromLaw_eq_sum [MeasurableSpace α] (adv : QueryAdversary (X × Y × W) α q) :
    adv.qromLaw =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (adv.run (oracleQuery H)).outcomeMeasure adv.init := by
  rw [qromLaw, outcomeLaw_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The relabelled law of the quantum random-oracle model is the average, over all `|Y| ^ |X|`
functions, of the outcome measures of the relabelled runs. -/
theorem qromLawWith_eq_sum [MeasurableSpace β] (adv : QueryAdversary (X × Y × W) α q)
    (f : (X → Y) → α → β) :
    adv.qromLawWith f =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, ((adv.run (oracleQuery H)).map (f H)).outcomeMeasure adv.init := by
  rw [qromLawWith, outcomeLawWith_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The law of the quantum random-oracle model has total mass the trace of the initial
substate. -/
theorem qromLaw_apply_univ [MeasurableSpace α] (adv : QueryAdversary (X × Y × W) α q) :
    adv.qromLaw Set.univ = ENNReal.ofReal adv.init.matrix.trace.re :=
  adv.outcomeLaw_apply_univ lossless_oracleQuery

/-! ### No queries -/

/-- **No queries, no knowledge of the oracle.** In the quantum random-oracle model, an adversary
that makes no query and outputs a guess, an input `x a` with a value `y a`, satisfies
`y a = H (x a)` with probability the trace of its initial substate divided by `|Y|`. -/
theorem qromLawWith_guess_zero (adv : QueryAdversary (X × Y × W) α 0) (x : α → X) (y : α → Y) :
    adv.qromLawWith (fun H a ↦ y a = H (x a)) {True} =
      ENNReal.ofReal adv.init.matrix.trace.re / Fintype.card Y := by
  have hrun : ∀ H : X → Y,
      adv.run (oracleQuery H) = (adv.step 0).bind fun _ ↦ adv.final := fun _ ↦ rfl
  rw [qromLawWith, outcomeLawWith_apply _ _ _ (MeasurableSet.singleton True)]
  simp only [hrun]
  rw [sum_outcomeMeasure_map_guess,
    ((adv.lossless_step 0).bind fun _ ↦ adv.lossless_final) adv.init.matrix]

/-- In the quantum random-oracle model, an adversary that starts from a normalized state, makes
no query and outputs a guess `(x, y)` satisfies `y = H x` with probability `1 / |Y|`. -/
theorem qromLawWith_guess_zero_of_trace_eq_one (adv : QueryAdversary (X × Y × W) (X × Y) 0)
    (h : adv.init.matrix.trace = 1) :
    adv.qromLawWith (fun H a ↦ a.2 = H a.1) {True} = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [qromLawWith_guess_zero adv Prod.fst Prod.snd, h]
  simp

end sampled

/-! ### The oracle is only seen where it is queried -/

/-- The queries of `adv` in the run against `Q` stay within the set `S` of query inputs: before
every query, the substate of the register is supported on the query inputs in `S`. -/
@[expose]
def QueriesWithin (adv : QueryAdversary (X × Y × W) α q) (S : Set X)
    (Q : SubInstrument (X × Y × W) (X × Y × W) Unit) : Prop :=
  ∀ i : Fin q, QuerySupportedOn S (adv.stateAfterStep Q i.castSucc).matrix

variable {S : Set X} {H H' : X → Y}

/-- If the queries of the adversary against `H` stay within `S` and `H'` agrees with `H` on `S`,
the runs against `H` and `H'` pass through the same substates. -/
theorem stateAfterStep_oracleQuery_eq_of_eqOn (adv : QueryAdversary (X × Y × W) α q)
    (hS : adv.QueriesWithin S (oracleQuery H)) (hH : Set.EqOn H H' S) (i : Fin (q + 1)) :
    adv.stateAfterStep (oracleQuery H') i = adv.stateAfterStep (oracleQuery H) i :=
  adv.stateAfterStep_congr (fun j ↦ (post_oracleQuery_congr hH (hS j)).symm) i

/-- Staying within `S` transfers to any function that agrees on `S`. -/
theorem QueriesWithin.of_eqOn {adv : QueryAdversary (X × Y × W) α q}
    (hS : adv.QueriesWithin S (oracleQuery H)) (hH : Set.EqOn H H' S) :
    adv.QueriesWithin S (oracleQuery H') := fun i ↦ by
  rw [adv.stateAfterStep_oracleQuery_eq_of_eqOn hS hH]
  exact hS i

/-- **The oracle is only seen where it is queried.** If the queries of the adversary against `H`
stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` have the same
outcome measure. -/
theorem outcomeMeasure_run_oracleQuery_eq_of_eqOn [MeasurableSpace α]
    (adv : QueryAdversary (X × Y × W) α q) (hS : adv.QueriesWithin S (oracleQuery H))
    (hH : Set.EqOn H H' S) :
    (adv.run (oracleQuery H')).outcomeMeasure adv.init =
      (adv.run (oracleQuery H)).outcomeMeasure adv.init :=
  adv.outcomeMeasure_run_congr fun j ↦ (post_oracleQuery_congr hH (hS j)).symm

end qrom

end QueryAdversary

end Quantum
