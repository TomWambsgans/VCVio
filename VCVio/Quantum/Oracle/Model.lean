/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.UniformTable
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.Quantum.Comp.QueryBound
public import VCVio.Quantum.Comp.Simulation
public import VCVio.Quantum.Oracle.Unitary

/-!
# The quantum random-oracle model

An oracle is realized by a family of runtimes indexed by a sampled value.
`Quantum.sampledLaw R x ρ` draws the value `ω` uniformly, with VCVio's `$ᵗ`, and observes the
run of the program `x` against the runtime `R ω` from `ρ` (`Quantum.QuantumRuntime.outcomeLaw`).
Another realization of the oracle is another family of runtimes for the same signature, and
"same outcome law" is an equation between two values of `Quantum.sampledLaw`.

The quantum random-oracle model is the instance for the signature `Quantum.qromSpec X Y`, with
one port acting on `X × Y`, in which the sampled value is a function `H : X → Y` and the runtime
`Quantum.xorRuntime H` answers each call with the oracle unitary of `H`
(`Quantum.qromLaw`). Programs are general quantum programs (`Quantum.QuantumComp`): adaptive,
with their own registers, and with any number of calls on each path.

Events that mention the sampled value, such as "the program's guess `(x, y)` satisfies
`y = H x`", are measured by `Quantum.sampledLawWith`, which relabels the output of each run by a
function that sees the sampled value.

## Main results

* `Quantum.qromLaw_eq_sum`: the law is the average over all functions of the outcome laws of the
  runs.
* `Quantum.qromLaw_apply_univ`: against every function, a lossless run gives total mass the trace
  of the program's initial substate; `Quantum.isProbabilityMeasure_qromLaw` for a lossless
  program from a normalized state.
* `Quantum.run_xorRuntime_eq_of_isQueryBound_zero`: a program with query budget zero runs to the
  same subinstrument against every function.
* `Quantum.qromLawWith_guess_zero`: with query budget zero, a guess `(x, y)` satisfies `y = H x`
  with probability the total weight of the run divided by `|Y|`; `1 / |Y|` for a lossless program
  from a normalized state (`Quantum.qromLawWith_guess_zero_of_trace_eq_one`).
* `Quantum.outcomeLaw_xorRuntime_eq_of_eqOn`: if every call along the run against `H` receives
  an operator supported on the query inputs in `S` (`Quantum.QueriesWithin`), the run against any
  `H'` that agrees with `H` on `S` has the same outcome law, and the same joint post-states.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

namespace Quantum

variable {spec : QuantumOracleSpec} {A B : QReg} {α β : Type}

/-! ## Outcome laws against a sampled runtime -/

section sampled

variable {Ω : Type} [SampleableType Ω]

/-- The law of the output of `x`, relabelled by a function that sees the sampled value, when `ω`
is drawn uniformly and the oracle is realized by the runtime `R ω`: the mixture over `ω` of the
outcome laws of `x.map (f ω)` against `R ω` from `ρ`. -/
@[expose]
noncomputable def sampledLawWith [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) (f : Ω → α → β) : Measure β :=
  letI : MeasurableSpace Ω := ⊤
  (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).outcomeLaw (x.map (f ω)) ρ

/-- The law of the output of `x` when `ω` is drawn uniformly and the oracle is realized by the
runtime `R ω`: the mixture over `ω` of the outcome laws of `x` against `R ω` from `ρ`. -/
@[expose]
noncomputable def sampledLaw [MeasurableSpace α] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) : Measure α :=
  letI : MeasurableSpace Ω := ⊤
  (𝒟[$ᵗ Ω]).bind fun ω ↦ (R ω).outcomeLaw x ρ

/-- Relabelling the output without looking at the sampled value or changing the output gives the
outcome law. -/
theorem sampledLawWith_id [MeasurableSpace α] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) :
    sampledLawWith R x ρ (fun _ a ↦ a) = sampledLaw R x ρ := by
  simp only [sampledLawWith, sampledLaw]
  congr 1
  funext ω
  rw [show (fun a : α ↦ a) = id from rfl, QuantumComp.map_id]

section fintype

variable [Fintype Ω]

/-- The relabelled law of a measurable set averages, over the sampled values, its measure under
the relabelled runs. -/
theorem sampledLawWith_apply [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) (f : Ω → α → β) {s : Set β}
    (hs : MeasurableSet s) :
    sampledLawWith R x ρ f s =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).outcomeLaw (x.map (f ω)) ρ s := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledLawWith, SampleableType.evalDist_uniformSample, uniformOn_univ_bind_apply _ _ hs]

/-- The relabelled law is the average, over the sampled values, of the outcome laws of the
relabelled runs. -/
theorem sampledLawWith_eq_sum [MeasurableSpace β] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) (f : Ω → α → β) :
    sampledLawWith R x ρ f =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).outcomeLaw (x.map (f ω)) ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledLawWith_apply _ _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, Finset.mul_sum]

/-- The law of a measurable set averages, over the sampled values, its measure under the runs. -/
theorem sampledLaw_apply [MeasurableSpace α] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) {s : Set α} (hs : MeasurableSet s) :
    sampledLaw R x ρ s = ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).outcomeLaw x ρ s := by
  let : MeasurableSpace Ω := ⊤
  rw [sampledLaw, SampleableType.evalDist_uniformSample, uniformOn_univ_bind_apply _ _ hs]

/-- The law is the average, over the sampled values, of the outcome laws of the runs. -/
theorem sampledLaw_eq_sum [MeasurableSpace α] (R : Ω → QuantumRuntime spec)
    (x : QuantumComp spec A B α) (ρ : SubState A) :
    sampledLaw R x ρ = (Fintype.card Ω : ℝ≥0∞)⁻¹ • ∑ ω, (R ω).outcomeLaw x ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [sampledLaw_apply _ _ _ hs, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, Finset.mul_sum]

end fintype

/-- When every run is lossless and every initial substate has trace `c`, the law has total mass
the trace of `ρ` times `c`. -/
theorem sampledLaw_apply_univ [MeasurableSpace α] {R : Ω → QuantumRuntime spec}
    {x : QuantumComp spec A B α} (h : ∀ ω, ((R ω).run x).Lossless) {c : ℝ}
    (hc : ∀ ω, (R ω).init.matrix.trace.re = c) (ρ : SubState A) :
    sampledLaw R x ρ Set.univ = ENNReal.ofReal (ρ.matrix.trace.re * c) := by
  let : Fintype Ω := Fintype.ofFinite Ω
  rw [sampledLaw_apply _ _ _ MeasurableSet.univ]
  simp only [(R _).outcomeLaw_apply_univ_of_lossless (h _), hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

end sampled

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
divided by `|Y|`: for a subinstrument `P` on a substate `ρ`, averaging over all functions `H` the
weight with which the output `a` of `P` satisfies `y a = H (x a)` gives the trace of the total
output of `P` on `ρ` divided by `|Y|`. -/
theorem sum_outcomeMeasure_map_guess {M N : Type*} [Fintype M] [Fintype N]
    (P : SubInstrument M N α) (ρ : SubState M) (x : α → X) (y : α → Y) :
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

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The signature of a random oracle `X → Y`: one port, whose call acts on the query register
`X × Y` and returns no classical result. -/
@[expose]
def qromSpec (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    QuantumOracleSpec where
  Port := Unit
  In _ := QReg.of (X × Y)
  Out _ := QReg.of (X × Y)
  Result _ := Unit

variable [AddCommGroup Y]

/-- The runtime of the oracle unitary of `H : X → Y`: a trivial private register, and each call
applies `|x, y⟩ ↦ |x, y + H x⟩` to the query register. -/
@[expose]
noncomputable def xorRuntime (H : X → Y) : QuantumRuntime (qromSpec X Y) where
  D := QReg.of Unit
  init := SubState.basis ()
  step _ := (oracleQuery H).frame Unit

/-- The step of the oracle runtime is the oracle unitary, framed by the trivial register. -/
theorem xorRuntime_step (H : X → Y) (i : Unit) :
    (xorRuntime H).step i = (oracleQuery H).frame Unit :=
  rfl

/-- The private register of the oracle runtime starts in its unique basis state. -/
theorem xorRuntime_init (H : X → Y) : (xorRuntime H).init = SubState.basis () :=
  rfl

/-- The steps of the oracle runtime are lossless. -/
theorem lossless_xorRuntime_step (H : X → Y) (i : Unit) : ((xorRuntime H).step i).Lossless :=
  (lossless_oracleQuery H).frame Unit

/-- A lossless program runs against the oracle runtime to a lossless subinstrument. -/
theorem lossless_run_xorRuntime {x : QuantumComp (qromSpec X Y) A B α} (hx : x.Lossless)
    (H : X → Y) : ((xorRuntime H).run x).Lossless :=
  (xorRuntime H).lossless_run hx (lossless_xorRuntime_step H)

/-- The initial substate of the oracle runtime has trace one. -/
theorem trace_re_xorRuntime_init (H : X → Y) : (xorRuntime H).init.matrix.trace.re = 1 :=
  (congrArg Complex.re (SubState.trace_basis (A := Unit) ())).trans Complex.one_re

section sampled

variable [SampleableType (X → Y)]

/-- The law of the output of `x` from `ρ` in the quantum random-oracle model, relabelled by a
function that sees the random function: `H : X → Y` is drawn uniformly, the program runs against
the oracle unitary of `H`, and its output `a` is reported as `f H a`. -/
@[expose]
noncomputable def qromLawWith [MeasurableSpace β] (x : QuantumComp (qromSpec X Y) A B α)
    (ρ : SubState A) (f : (X → Y) → α → β) : Measure β :=
  sampledLawWith xorRuntime x ρ f

/-- The law of the output of `x` from `ρ` in the quantum random-oracle model: `H : X → Y` is
drawn uniformly and the program runs against the oracle unitary of `H`. -/
@[expose]
noncomputable def qromLaw [MeasurableSpace α] (x : QuantumComp (qromSpec X Y) A B α)
    (ρ : SubState A) : Measure α :=
  sampledLaw xorRuntime x ρ

/-- Relabelling the output without looking at the random function or changing the output gives
the law of the quantum random-oracle model. -/
theorem qromLawWith_id [MeasurableSpace α] (x : QuantumComp (qromSpec X Y) A B α)
    (ρ : SubState A) : qromLawWith x ρ (fun _ a ↦ a) = qromLaw x ρ :=
  sampledLawWith_id _ x ρ

/-- The law of the quantum random-oracle model is the average, over all `|Y| ^ |X|` functions,
of the outcome laws of the runs against their oracle unitaries. -/
theorem qromLaw_eq_sum [MeasurableSpace α] (x : QuantumComp (qromSpec X Y) A B α)
    (ρ : SubState A) :
    qromLaw x ρ =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (xorRuntime H).outcomeLaw x ρ := by
  rw [qromLaw, sampledLaw_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- The relabelled law of the quantum random-oracle model is the average, over all `|Y| ^ |X|`
functions, of the outcome laws of the relabelled runs. -/
theorem qromLawWith_eq_sum [MeasurableSpace β] (x : QuantumComp (qromSpec X Y) A B α)
    (ρ : SubState A) (f : (X → Y) → α → β) :
    qromLawWith x ρ f =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (xorRuntime H).outcomeLaw (x.map (f H)) ρ := by
  rw [qromLawWith, sampledLawWith_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- When the run against every function is lossless, the law of the quantum random-oracle model
has total mass the trace of the initial substate. -/
theorem qromLaw_apply_univ [MeasurableSpace α] {x : QuantumComp (qromSpec X Y) A B α}
    (h : ∀ H, ((xorRuntime H).run x).Lossless) (ρ : SubState A) :
    qromLaw x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [qromLaw, sampledLaw_apply_univ h trace_re_xorRuntime_init, mul_one]

/-- The law of a lossless program has total mass the trace of the initial substate. -/
theorem qromLaw_apply_univ_of_lossless [MeasurableSpace α]
    {x : QuantumComp (qromSpec X Y) A B α} (hx : x.Lossless) (ρ : SubState A) :
    qromLaw x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re :=
  qromLaw_apply_univ (lossless_run_xorRuntime hx) ρ

/-- When the run against every function is lossless and the initial state is normalized, the
law of the quantum random-oracle model is a probability measure. -/
theorem isProbabilityMeasure_qromLaw [MeasurableSpace α] {x : QuantumComp (qromSpec X Y) A B α}
    (h : ∀ H, ((xorRuntime H).run x).Lossless) {ρ : SubState A} (hρ : ρ.matrix.trace = 1) :
    IsProbabilityMeasure (qromLaw x ρ) :=
  ⟨by rw [qromLaw_apply_univ h, hρ, Complex.one_re, ENNReal.ofReal_one]⟩

end sampled

/-! ### No queries -/

/-- **No queries, no dependence on the oracle.** A program with query budget zero runs to the
same subinstrument against every function. -/
theorem run_xorRuntime_eq_of_isQueryBound_zero {x : QuantumComp (qromSpec X Y) A B α}
    (hx : x.IsQueryBound 0) (H H' : X → Y) : (xorRuntime H).run x = (xorRuntime H').run x :=
  QuantumRuntime.run_congr_of_isQueryBound hx fun _ h ↦ absurd rfl h

/-- **No queries, no knowledge of the oracle.** In the quantum random-oracle model, a program with
query budget zero that outputs a guess, an input `gx a` with a value `gy a`, satisfies
`gy a = H (gx a)` with probability the total weight of its run divided by `|Y|`. The run does not
depend on the function (`run_xorRuntime_eq_of_isQueryBound_zero`); it is taken against `H₀`. -/
theorem qromLawWith_guess_zero [SampleableType (X → Y)] {x : QuantumComp (qromSpec X Y) A B α}
    (hx : x.IsQueryBound 0) (ρ : SubState A) (gx : α → X) (gy : α → Y) (H₀ : X → Y) :
    qromLawWith x ρ (fun H a ↦ gy a = H (gx a)) {True} =
      ENNReal.ofReal (((xorRuntime H₀).run x).total (ρ.prod (SubState.basis ())).matrix).trace.re /
        Fintype.card Y := by
  have hrun : ∀ H : X → Y, (xorRuntime H).outcomeLaw (x.map fun a ↦ gy a = H (gx a)) ρ =
      (((xorRuntime H₀).run x).map fun a ↦ gy a = H (gx a)).outcomeMeasure
        (ρ.prod (SubState.basis ())) := fun H ↦ by
    rw [QuantumRuntime.outcomeLaw, QuantumRuntime.run_map,
      run_xorRuntime_eq_of_isQueryBound_zero hx H H₀]
    rfl
  rw [qromLawWith, sampledLawWith_apply _ _ _ _ (MeasurableSet.singleton True)]
  simp only [hrun]
  exact sum_outcomeMeasure_map_guess _ _ gx gy

/-- A lossless program with query budget zero guesses a value of the random function with
probability the trace of its initial substate divided by `|Y|`. -/
theorem qromLawWith_guess_zero_of_lossless [SampleableType (X → Y)]
    {x : QuantumComp (qromSpec X Y) A B α} (hx : x.IsQueryBound 0) (hl : x.Lossless)
    (ρ : SubState A) (gx : α → X) (gy : α → Y) :
    qromLawWith x ρ (fun H a ↦ gy a = H (gx a)) {True} =
      ENNReal.ofReal ρ.matrix.trace.re / Fintype.card Y := by
  have h : (((xorRuntime 0).run x).total (ρ.prod (SubState.basis ())).matrix).trace =
      (ρ.prod (SubState.basis ())).matrix.trace :=
    lossless_run_xorRuntime hl 0 (ρ.prod (SubState.basis ())).matrix
  rw [qromLawWith_guess_zero hx ρ gx gy 0, h, SubState.trace_re_prod, SubState.trace_basis,
    Complex.one_re, mul_one]

/-- In the quantum random-oracle model, a lossless program with query budget zero that starts
from a normalized state and outputs a guess `(x, y)` satisfies `y = H x` with probability
`1 / |Y|`. -/
theorem qromLawWith_guess_zero_of_trace_eq_one [SampleableType (X → Y)]
    {x : QuantumComp (qromSpec X Y) A B (X × Y)} (hx : x.IsQueryBound 0) (hl : x.Lossless)
    {ρ : SubState A} (hρ : ρ.matrix.trace = 1) :
    qromLawWith x ρ (fun H a ↦ a.2 = H a.1) {True} = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  rw [qromLawWith_guess_zero_of_lossless hx hl ρ Prod.fst Prod.snd, hρ]
  simp

/-! ### The oracle is only seen where it is queried -/

/-- Every call along every branch of the run of `x` against `H` from `ρ` receives an operator
supported on the query inputs in `S`: before each call, the joint operator of the query
register, the runtime register and the carried remainder vanishes outside query inputs in `S`.
Branches of weight zero receive the zero operator and impose nothing. -/
@[expose]
def QueriesWithin (x : QuantumComp (qromSpec X Y) A B α) (S : Set X) (H : X → Y)
    (ρ : SubState A) : Prop :=
  (xorRuntime H).ForallQueries
    (fun _ E σ ↦ QuerySupportedOn (fun m : ((X × Y) × Unit) × E ↦ m.1.1.1) S σ) x
    (ρ.prod (SubState.basis ())).matrix

variable {S : Set X} {H H' : X → Y}

/-- On an operator supported on the query inputs in `S`, a call of the oracle runtime of `H`,
framed by any remainder, only depends on the restriction of `H` to `S`. -/
theorem xorRuntime_step_frame_congr (hH : Set.EqOn H H' S) (i : (qromSpec X Y).Port) (E : QReg)
    {σ : Matrix (((X × Y) × Unit) × E) (((X × Y) × Unit) × E) ℂ}
    (hσ : QuerySupportedOn (fun m : ((X × Y) × Unit) × E ↦ m.1.1.1) S σ) (r : Unit) :
    (((xorRuntime H).step i).frame E).branch r σ =
      (((xorRuntime H').step i).frame E).branch r σ := by
  change (((oracleQuery H).frame Unit).frame E).branch r σ =
    (((oracleQuery H').frame Unit).frame E).branch r σ
  rw [SubInstrument.branch_frame_apply, SubInstrument.branch_frame_apply,
    SubInstrument.branch_frame_apply, SubInstrument.branch_frame_apply, branch_oracleQuery_apply,
    branch_oracleQuery_apply]
  ext m m'
  rw [MatrixMap.amplify_apply _ σ m m', MatrixMap.amplify_apply _ σ m m',
    amplify_conj_oracleUnitary_congr hH
      (QuerySupportedOn.block (q := fun n : (X × Y) × Unit ↦ n.1.1) hσ m.2 m'.2)]

/-- **The oracle is only seen where it is queried.** If the calls of the run of `x` against `H`
from `ρ` stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` from `ρ`
have the same branches. -/
theorem run_branch_xorRuntime_eq_of_eqOn {x : QuantumComp (qromSpec X Y) A B α}
    {ρ : SubState A} (hS : QueriesWithin x S H ρ) (hH : Set.EqOn H H' S) (a : α) :
    ((xorRuntime H').run x).branch a (ρ.prod (SubState.basis ())).matrix =
      ((xorRuntime H).run x).branch a (ρ.prod (SubState.basis ())).matrix :=
  (QuantumRuntime.run_branch_apply_eq_of_forallQueries (D := QReg.of Unit)
    (σ₁ := SubState.basis ()) (σ₂ := SubState.basis ()) (s₁ := (xorRuntime H).step)
    (s₂ := (xorRuntime H').step) (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS
    a).symm

/-- **The oracle is only seen where it is queried.** If the calls of the run of `x` against `H`
from `ρ` stay within `S` and `H'` agrees with `H` on `S`, the runs against `H` and `H'` from `ρ`
have the same outcome law. -/
theorem outcomeLaw_xorRuntime_eq_of_eqOn [MeasurableSpace α]
    {x : QuantumComp (qromSpec X Y) A B α} {ρ : SubState A} (hS : QueriesWithin x S H ρ)
    (hH : Set.EqOn H H' S) : (xorRuntime H').outcomeLaw x ρ = (xorRuntime H).outcomeLaw x ρ :=
  (QuantumRuntime.outcomeLaw_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step)
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS).symm

/-- If the calls of the run of `x` against `H` from `ρ` stay within `S` and `H'` agrees with `H`
on `S`, the runs against `H` and `H'` from `ρ` leave the same joint post-states. -/
theorem jointPost_xorRuntime_eq_of_eqOn {x : QuantumComp (qromSpec X Y) A B α}
    {ρ : SubState A} (hS : QueriesWithin x S H ρ) (hH : Set.EqOn H H' S) (a : α) :
    (xorRuntime H').jointPost x ρ a = (xorRuntime H).jointPost x ρ a :=
  (QuantumRuntime.jointPost_eq_of_forallQueries (D := QReg.of Unit) (σ := SubState.basis ())
    (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step)
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS a).symm

/-- Staying within `S` transfers to any function that agrees on `S`. -/
theorem QueriesWithin.of_eqOn {x : QuantumComp (qromSpec X Y) A B α} {ρ : SubState A}
    (hS : QueriesWithin x S H ρ) (hH : Set.EqOn H H' S) : QueriesWithin x S H' ρ :=
  QuantumRuntime.ForallQueries.of_congr (D := QReg.of Unit) (σ₁ := SubState.basis ())
    (σ₂ := SubState.basis ()) (s₁ := (xorRuntime H).step) (s₂ := (xorRuntime H').step)
    (fun i E _ hσ r ↦ xorRuntime_step_frame_congr hH i E hσ r) hS

end qrom

end Quantum
