/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldAssembly

/-!
# Outcome-preserving offline assembly regressions

The tests exercise extended masses, cross terms in amplitude aggregation, and the explicit
collision-coefficient comparison. They do not substitute arithmetic for the security theorem.
-/

public section

open Quantum Quantum.SaltedMerkle
open scoped ENNReal NNReal

/-- Zero coefficients annihilate even infinite mass allowances. -/
example : oldOfflineBound 16 0 ⊤ ⊤ 0 = 0 := oldOfflineBound_zero 16 ⊤ ⊤

/-- Four unit amplitudes have squared total sixteen, including all cross terms. -/
example : (∑' _ : Unit, (16 : ℝ≥0∞)) ≤
    ((∑' _ : Unit, (1 : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
      (∑' _ : Unit, (1 : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
      (∑' _ : Unit, (1 : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
      (∑' _ : Unit, (1 : ℝ≥0∞)) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) := by
  apply tsum_le_sq_of_four_amplitudes
  intro _
  simp only [ENNReal.one_rpow]
  rw [ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The FIX comparison starts at total budget four and does not require finite masses. -/
example (w e : ℝ≥0∞) : oldOfflineBound 16 4 w e 2 ≤ oldOfflineFixBound 16 4 w e 2 :=
  oldOfflineBound_le_fix (by norm_num) (by norm_num) w e 2

/-- The terminal component allowance alone gives a quarter at sixteen outputs and one call. -/
example : oldOfflineBound 16 1 0 0 0 = 1 / 4 := by
  have hs : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [oldOfflineBound, oldChangingFraction, oldLeakagePolynomial]
  have hroot : ENNReal.ofReal (1 / 16 : ℝ) ^ (1 / 2 : ℝ) = (1 / 4 : ℝ≥0∞) := by
    simp only [one_div]
    rw [ENNReal.ofReal_rpow_inv_two]
    norm_num [Real.sqrt_div, hs, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [hroot]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)) (by finiteness)).mp
  rw [ENNReal.toReal_min (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow]
