/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import VCVio.Quantum.VC.Merkle.Online

/-!
# Public-import checks for recording grades and online constants

The declarations are consumed through an ordinary import. The numerical examples check the
zero errors at budgets zero and one, the odd-weight sum, the coefficient 24, and the cap.
They do not assert an online indistinguishability theorem.
-/

public section

open Quantum
open scoped ENNReal

#check RecReg.swapEquiv
#check RecReg.occupied_swap
#check RecReg.swap_eq_of_extract_eq_on_occupied
#check VCOracle.withRecord_jointPost_grade
#check VCOracle.withRecordME_jointPost_grade
#check compressedVCOracle_U_totalSize_le
#check SaltedMerkle.instability_onlineLabel_list_le
#check SaltedMerkle.instability_onlineLabel_empty
#check online_weighted_sum_sq_le

example : (Finset.range 6).sum onlineStepWeight = 25 := by
  norm_num [sum_onlineStepWeight]

example : merkleOnlineError 1024 3 2 = (3 / 16 : ℝ≥0∞) := by
  norm_num [merkleOnlineError]
  rw [min_eq_right ((ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num))]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

example : merkleOnlineError 16 3 2 = 1 := by
  norm_num [merkleOnlineError]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  norm_num

example : merkleOnlineError 1024 0 ⊤ = 0 ∧ merkleOnlineError 1024 1 ⊤ = 0 := by
  simp

example : (24 / (1024 : ℝ)) *
    (∑ j ∈ Finset.range 3, Real.sqrt ((onlineStepWeight j : ℝ) * onlineStepWeight j)) ^ 2 =
      3 / 8 := by
  norm_num [Finset.sum_range_succ, onlineStepWeight, Real.sqrt_mul_self]

example (ME : MultiExtractor 0 Unit (fun _ ↦ Unit) Unit)
    (R : RecReg 0 Unit (fun _ ↦ Unit) Bool) : RecReg.swap ME () R = R := by
  apply Prod.ext
  · funext q
    have hp := q.1.len_pos
    have hl := q.1.len_le
    omega
  · funext qt
    have hp := qt.1.1.len_pos
    have hl := qt.1.1.len_le
    omega

end
