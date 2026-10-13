/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Classical

/-!
# Quantum random-oracle regression tests

Oracles `Fin 2 → Fin 2`, queried on the register `Fin 2 × Fin 2 × Unit`.

* Deutsch's algorithm reports `H 0 + H 1` with one query and certainty, so it tells constant
  oracles from balanced ones. It is presented with the Hadamard gates absorbed into the initial
  state `|+⟩|-⟩` and into the final measurement of the query register in the `|±⟩` basis.
* The classical algorithm that queries `0` and returns the answer, run as a one-query adversary,
  reports `H 0` with certainty, and its law in the quantum random-oracle model is its output
  measure under the lazily sampled random oracle.
* A zero-query adversary guesses a point of a uniformly sampled oracle with probability `1 / 2`.
-/

public section

open Quantum Matrix MeasureTheory OracleSpec
open scoped ComplexOrder ENNReal

namespace VCVioTest.QuantumOracle

/-! ## Deutsch's algorithm -/

/-- The register of Deutsch's algorithm: one query qubit and one response qubit. -/
abbrev Reg : Type := Fin 2 × Fin 2 × Unit

/-- The sign `(-1) ^ y` of a bit. -/
def sgn (y : Fin 2) : ℂ :=
  if y = 0 then 1 else -1

/-- The amplitudes of the state `|+⟩|-⟩`. -/
noncomputable def amp : Reg → ℂ :=
  fun m ↦ sgn m.2.1 / 2

/-- The projector onto `|+⟩` (for `b = 0`) or `|-⟩` (for `b = 1`) of the query qubit. -/
noncomputable def proj (b : Fin 2) : Matrix Reg Reg ℂ :=
  Matrix.of fun m m' ↦ if m.2 = m'.2 then sgn (b * (m.1 + m'.1)) / 2 else 0

theorem eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The projectors onto `|+⟩` and `|-⟩` satisfy the completeness relation. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ b, (proj b)ᴴ * proj b = 1 := by
  ext ⟨x, y, u⟩ ⟨x', y', u'⟩
  rcases eq_zero_or_one x with rfl | rfl <;> rcases eq_zero_or_one y with rfl | rfl <;>
    rcases eq_zero_or_one x' with rfl | rfl <;> rcases eq_zero_or_one y' with rfl | rfl <;>
    norm_num [Fin.sum_univ_two, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, proj,
      sgn, map_ofNat]

/-- The state `|+⟩|-⟩`. -/
noncomputable def plusMinus : SubState Reg where
  matrix := vecMulVec amp (star amp)
  posSemidef := Matrix.posSemidef_vecMulVec_self_star amp
  trace_re_le_one := by
    norm_num [Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, amp, sgn]

/-- Deutsch's algorithm: start in `|+⟩|-⟩`, query once, and measure the query qubit in the
`|±⟩` basis. -/
noncomputable def deutsch : QueryAdversary Reg (Fin 2) 1 where
  init := plusMinus
  step _ := SubInstrument.pure ()
  lossless_step _ := SubInstrument.lossless_pure ()
  final := SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj
  lossless_final := SubInstrument.lossless_ofKraus _ _

/-- The weight of a Kraus branch on a pure state is the squared norm of the image vector. -/
theorem trace_conj_vecMulVec {A B : Type} [Fintype A] [Fintype B] (K : Matrix B A ℂ)
    (v : A → ℂ) :
    (MatrixMap.conj K (vecMulVec v (star v))).trace = ∑ i, (K *ᵥ v) i * star ((K *ᵥ v) i) := by
  rw [MatrixMap.conj_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
    Matrix.trace_vecMulVec]
  rfl

/-- After the query, the measurement reports `H 0 + H 1` with weight one. -/
theorem trace_conj_proj (H : Fin 2 → Fin 2) (b : Fin 2) :
    (MatrixMap.conj (proj b)
      (MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)))).trace =
      if b = H 0 + H 1 then 1 else 0 := by
  have h : MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) =
      vecMulVec (fun m ↦ amp ((oracleEquiv H).symm m))
        (star fun m ↦ amp ((oracleEquiv H).symm m)) := by
    rw [oracleUnitary, conj_basisMatrix_equiv]
    rfl
  rw [h, trace_conj_vecMulVec]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    rcases eq_zero_or_one b with rfl | rfl <;>
    norm_num [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, proj, amp, sgn,
      oracleEquiv_symm_apply, h0, h1]

/-- Deutsch's algorithm reports `H 0 + H 1` with certainty. -/
theorem outcomeMeasure_deutsch (H : Fin 2 → Fin 2) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init = Measure.dirac (H 0 + H 1) := by
  rw [QueryAdversary.outcomeMeasure_run, show Fin.last 1 = (0 : Fin 1).succ from rfl,
    QueryAdversary.stateAfterStep_succ]
  change deutsch.final.outcomeMeasure ((SubInstrument.pure ()).post
    ((oracleQuery H).post ((SubInstrument.pure ()).post plusMinus ()) ()) ()) = _
  rw [SubInstrument.post_pure_self, SubInstrument.post_pure_self,
    SubInstrument.outcomeMeasure_eq_sum_univ, Fin.sum_univ_two]
  have h : ∀ b, (deutsch.final.branch b ((oracleQuery H).post plusMinus ()).matrix).trace =
      if b = H 0 + H 1 then 1 else 0 := fun b ↦ by
    have h₁ : ((oracleQuery H).post plusMinus ()).matrix =
        MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) := by
      simp [MatrixMap.conj_apply, plusMinus]
    rw [h₁]
    change ((SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj).branch b _).trace = _
    rw [SubInstrument.branch_ofKraus_apply]
    exact trace_conj_proj H b
  rw [h, h]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [h0, h1]

/-- On a constant oracle, Deutsch's algorithm reports `0` with certainty. -/
example (H : Fin 2 → Fin 2) (h : H 0 = H 1) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init {0} = 1 := by
  rcases eq_zero_or_one (H 1) with h1 | h1 <;> simp [outcomeMeasure_deutsch, h, h1]

/-- On a balanced oracle, Deutsch's algorithm reports `1` with certainty. -/
example (H : Fin 2 → Fin 2) (h : H 0 ≠ H 1) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init {1} = 1 := by
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [outcomeMeasure_deutsch, h0, h1] at h ⊢

/-! ## A classical one-query algorithm -/

/-- The classical algorithm that queries the oracle at `0` and returns the answer. -/
def queryZero : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) :=
  liftM ((Fin 2 →ₒ Fin 2).query 0)

/-- The algorithm makes at most one query. -/
theorem isTotalQueryBound_queryZero : OracleComp.IsTotalQueryBound queryZero 1 := by
  rw [queryZero, ← bind_pure (liftM _), OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- Run as a one-query adversary against the oracle unitary of `H`, the algorithm reports `H 0`
with certainty. -/
example (H : Fin 2 → Fin 2) :
    ((QueryAdversary.ofOracleComp queryZero 1).run (oracleQuery H)).outcomeMeasure
      (QueryAdversary.ofOracleComp queryZero 1).init = Measure.dirac (H 0) :=
  QueryAdversary.outcomeMeasure_run_ofOracleComp isTotalQueryBound_queryZero H

/-- The law of the algorithm in the quantum random-oracle model is its output measure under the
lazily sampled random oracle. -/
example :
    (QueryAdversary.ofOracleComp queryZero 1).qromLaw =
      𝒟[(simulateQ randomOracle queryZero).run' ∅] :=
  QueryAdversary.qromLaw_ofOracleComp_eq_randomOracle isTotalQueryBound_queryZero

/-! ## Guessing without queries -/

/-- A zero-query adversary started in a state of trace one guesses a point of the oracle with
probability `1 / 2`. -/
example (adv : QueryAdversary Reg (Fin 2 × Fin 2) 0) (h : adv.init.matrix.trace = 1) :
    adv.qromLawWith (fun H a ↦ a.2 = H a.1) {True} = 2⁻¹ := by
  simpa using adv.qromLawWith_guess_zero_of_trace_eq_one h

end VCVioTest.QuantumOracle
