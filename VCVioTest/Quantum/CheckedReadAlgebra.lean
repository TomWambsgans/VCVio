/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.CheckedReadBound

/-!
# Checked-read algebra at small answer alphabets

The singleton alphabet still distinguishes an empty decompressed cell from the filled zero
answer. The negative trivial character is a nonidentity block even in this case.
-/

public section

open Quantum Matrix

namespace VCVioTest.CheckedReadAlgebra

/-- At one answer, the negative trivial block has residual squared norm four. -/
theorem singleton_negative_trivial :
    ∑ a, ‖checkedReadPhaseCell (0 : AddChar (ZMod 1) ℂ) (-1) (some 0) a -
      if a = some 0 then -1 else 0‖ ^ 2 = 4 := by
  simpa using sum_norm_checkedReadPhaseCell_zero_neg_one_sub_sq (0 : ZMod 1)

/-- The empty decompressed sector is fixed by the negative trivial block. -/
theorem negative_trivial_filled_entry :
    checkedReadPhaseCell (0 : AddChar (ZMod 1) ℂ) (-1) (some 0) (some 0) = 1 := by
  rw [checkedReadPhaseCell_zero_neg_one]
  norm_num [checkedReadEmptyCell_apply, cellAmp]

/-- The same block negates the compressed empty basis vector. -/
theorem negative_trivial_empty_entry :
    checkedReadPhaseCell (0 : AddChar (ZMod 1) ℂ) (-1) none none = -1 := by
  rw [checkedReadPhaseCell_zero_neg_one]
  simp [checkedReadEmptyCell_apply]

/-- With one answer, the ordinary zero branch retains the entire private state. -/
theorem singleton_ordinary_zero :
    compressedOracle Unit (ZMod 1)
      (((), 0), Database.ofFun (fun _ ↦ 0)) (((), 0), Database.ofFun (fun _ ↦ 0)) = 1 := by
  rw [compressedOracle_fresh_zero]
  simp [Matrix.add_apply, checkedReadProjector_apply, cellAmp]

/-- The checked filled-zero branch rejects the state retained by the ordinary zero branch. -/
theorem singleton_checked_zero :
    checkedReadUnitary (X := Unit) (Y := ZMod 1)
      (((), (0, 1)), Database.ofFun (fun _ ↦ 0))
      (((), (0, 0)), Database.ofFun (fun _ ↦ 0)) = 0 := by
  rw [checkedReadUnitary_fresh_some]
  simp [checkedReadProjector_apply]


/-- The actual dilation has the signed-cell Fourier form even for a singleton answer type. -/
example (χ : AddChar (ZMod 1 × ZMod 2) ℂ) (D D' : Database Unit (ZMod 1)) :
    (checkedReadFourier * checkedReadUnitary *
      (checkedReadFourier (X := Unit) (Y := ZMod 1))ᴴ :
      Matrix ((Unit × AddChar (ZMod 1 × ZMod 2) ℂ) × Database Unit (ZMod 1))
        ((Unit × AddChar (ZMod 1 × ZMod 2) ℂ) × Database Unit (ZMod 1)) ℂ)
      (((), χ), D') (((), χ), D) =
      checkedReadPhaseCell (checkedReadAnswerChar χ) (χ (0, 1)) (D' ()) (D ()) := by
  rw [checkedReadFourier_conj_apply]
  simp

#check @DatabaseSupportedOn.conj_checkedReadProjector
#check @QuerySupportedOn.conj_selectedCheckedReadProjector
#check @truncatedCheckedRead_eq
#check @truncatedValidity_eq

end VCVioTest.CheckedReadAlgebra
