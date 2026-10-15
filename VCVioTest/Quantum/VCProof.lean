/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Consistency

/-!
# Tests for the consistency projectors and the proofs of Lemmas 9.2 and 9.3

Checks of the public interface of `VCVio.Quantum.Oracle.Compressed.Consistency` (eq. (26) of the
notes on ePrint 2025/2166, sharpening Lemma 9.5):

* the exact discrepancy `‖P̂ - P‖² = 1 - (1 - 1/N)^2` for one prescribed cell, with `N = 3`;
* an inconsistent prescription has both projectors zero;
* the empty prescription has `P = P̂ = 1`.
-/

public section

open Quantum Matrix
open scoped Matrix.Norms.L2Operator

namespace VCVioTest.QuantumVCProof

/-! ## Consistency projectors -/

/-- One prescribed cell, `true ↦ 1`, for databases `Bool → Option (ZMod 3)`. -/
abbrev io₁ : List (Bool × ZMod 3) := [(true, 1)]

/-- With one prescribed cell and `N = 3`, the discrepancy is exactly `1 - (2/3)² = 5/9`. -/
example : ‖compressedCheckProjector io₁ - checkProjector (ZMod 3) io₁‖ ^ 2 = 5 / 9 := by
  have h : ConsistentIO io₁ := consistentIO_singleton _
  have hcard : (ioCells io₁).card = 1 := rfl
  rw [l2_opNorm_compressedCheckProjector_sub_sq h, hcard, ZMod.card]
  norm_num

/-- Two different outputs at the same input. -/
abbrev ioBad : List (Bool × ZMod 3) := [(true, 0), (true, 1)]

/-- The prescription `ioBad` is inconsistent. -/
theorem not_consistentIO_ioBad : ¬ ConsistentIO ioBad := fun h ↦
  absurd (h (true, 0) (by simp) (true, 1) (by simp) rfl) (by decide)

/-- An inconsistent prescription has zero projector. -/
example : checkProjector (ZMod 3) ioBad = 0 :=
  checkProjector_eq_zero_of_not_consistentIO not_consistentIO_ioBad

/-- An inconsistent prescription has zero compressed projector. -/
example : compressedCheckProjector ioBad = 0 :=
  compressedCheckProjector_eq_zero_of_not_consistentIO not_consistentIO_ioBad

/-- The empty prescription: both projectors are the identity. -/
example : compressedCheckProjector ([] : List (Bool × ZMod 3)) -
    checkProjector (ZMod 3) ([] : List (Bool × ZMod 3)) = 0 := by
  simp

end VCVioTest.QuantumVCProof
