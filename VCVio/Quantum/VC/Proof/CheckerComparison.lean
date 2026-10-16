/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Repeatability
import all VCVio.Quantum.VC.Proof.Repeatability
import all VCVio.Quantum.VC.Compressed
import all VCVio.Quantum.Oracle.ClassicalRepeatability

/-!
# The actual checker of the old compressed oracle

The classical checker of ePrint 2025/2166, Definition 8.1, PDF page 52, has an accepting
projector that includes empty sectors for zero answers. The filled checker instead requires
`some y` at every prescribed cell before compression. Their difference is positive and supported
on invalid sectors, as in the repair note FIX (29), (31). These are identities on the entire
private space, with no population or reachable-state hypothesis.

The filled versus partial discrepancy uses the exact constant of the bounds note (26),
sharpening ePrint 2025/2166, Lemma 9.5, PDF page 61. Conflicting prescriptions are included.
These operator statements alone do not establish the offline game of Lemma 9.6, PDF page 62.
-/

public section

open Matrix OracleComp
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

namespace Quantum
namespace ProjectiveClassicalAnswers

variable {P : Type*} {In : P → QReg} {E : EmulatedOracle P In}
  {X Y : Type} [Fintype Y] [DecidableEq Y]
  (H : ProjectiveClassicalAnswers E X Y)

/-- The actual classical calls associated with a projective answer interface. -/
noncomputable def classicalCall (B : QReg) : QueryImpl (X →ₒ Y) (QComp (uSpec P In) B B) :=
  fun x ↦ QComp.callBasis (H.query x).1 B (H.query x).2 (fun o _ ↦ H.read x o)

/-- The accepting branch of the complete checker fold. Calls continue after a failed comparison;
all rejected answer histories have zero contribution to the accepting branch. -/
theorem actual_fold_accept (B : QReg) (io : List (X × Y)) (acc : Bool) :
    (E.toRuntime.run₂ .instruments
      ((io.foldlM checkIOStep acc).toQuantumAt (H.classicalCall B))).branch true =
        if acc then H.transcriptBranch B io else 0 := by
  induction io generalizing acc with
  | nil =>
    rw [List.foldlM_nil, toQuantumAt_pure, QuantumRuntime.run₂_pure]
    cases acc
    · exact SubInstrument.branch_pure_of_ne (by decide)
    · simp
  | cons p io ih =>
    have hp : ((p :: io).foldlM checkIOStep acc).toQuantumAt (H.classicalCall B) =
        (H.classicalCall B p.1).bind fun y ↦
          (io.foldlM checkIOStep (acc && decide (y = p.2))).toQuantumAt
            (H.classicalCall B) := by
      rw [List.foldlM_cons, checkIOStep, bind_assoc]
      simp only [pure_bind]
      exact toQuantumAt_query_bind (H.classicalCall B) p.1 _
    rw [hp, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply_univ,
      Finset.sum_eq_single p.2]
    · rw [ih]
      simp only [decide_true, Bool.and_true]
      cases acc
      · simp
      · simp only [↓reduceIte]
        rw [classicalCall, H.branch_eq]
        exact (H.transcriptBranch_cons B p io).symm
    · intro y _ hy
      rw [ih]
      simp [hy]
    · simp

/-- The actual classical `checkIO` accepts on the product of its answer projectors, including
repeated and contradictory prescriptions, on any entangled reference/private input matrix. -/
theorem actual_accept_eq_projectorProduct (B : QReg) (io : List (X × Y)) :
    (E.toRuntime.run₂ .instruments
      ((checkIO io).toQuantumAt (H.classicalCall B))).branch true =
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.projector io) := by
  simpa only [checkIO, ↓reduceIte, transcriptBranch] using H.actual_fold_accept B io true

end ProjectiveClassicalAnswers

namespace CompressedReplay

section lookup

variable {k : ℕ} {X Y : Type} [AddCommGroup Y]

private theorem filled_implies_lookup (D : Fin k → Database X Y)
    (io : List ((Fin k × X) × Y)) (h : ∀ p ∈ io, D p.1.1 p.1.2 = some p.2) :
    ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 := by
  intro p hp
  simp [Database.lookup_apply, h p hp]

private theorem lookup_filled_of_valid (D : Fin k → Database X Y)
    (io : List ((Fin k × X) × Y)) (hv : ∀ j x, D j x ≠ none)
    (ha : ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2) :
    ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 := by
  intro p hp
  cases he : D p.1.1 p.1.2 with
  | none => exact False.elim (hv _ _ he)
  | some y => simpa [Database.lookup_apply, he] using ha p hp

private theorem indicator_bounds (A Q V : Prop) [Decidable A] [Decidable Q] [Decidable V]
    (hQA : Q → A) (hVAQ : V → A → Q) :
    (0 : ℂ) ≤ (if A then 1 else 0) - (if Q then 1 else 0) ∧
    (0 : ℂ) ≤ 1 - (if V then 1 else 0) -
      ((if A then 1 else 0) - (if Q then 1 else 0)) := by
  by_cases hA : A <;> by_cases hQ : Q <;> by_cases hV : V <;> simp_all

end lookup

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

/-- The accepting projector of the old oracle's classical checker. Empty cells read zero. -/
noncomputable def actualCheck [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 then 1 else 0) *
      compressDatabases k X Y

/-- The partial-database checker on a list spanning several oracle indices. -/
noncomputable def partialCheck (io : List ((Fin k × X) × Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal fun D ↦ if ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 then 1 else 0

/-- The filled checker is the compressed conjugate of the partial-database checker. -/
noncomputable def filledCheck (io : List ((Fin k × X) × Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y * partialCheck io * compressDatabases k X Y

/-- Validity means every decompressed cell is filled, across all oracle indices. -/
noncomputable def validProjector (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if ∀ j x, D j x ≠ none then 1 else 0) * compressDatabases k X Y

/-- The product of actual answer projectors is a conjugated lookup predicate. -/
theorem actualCheck_eq_projector [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    actualCheck io =
      (projectiveClassicalAnswers (k := k) (X := X) (Y := Y)).projector io := by
  change actualCheck io = (io.map fun p ↦ answer p.1 p.2).prod
  unfold actualCheck
  induction io with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.not_mem_nil, false_imp_iff,
      implies_true, ite_true, diagonal_one, Matrix.mul_one]
    exact compressDatabases_mul_self ..
  | cons p io ih =>
    rw [List.map_cons, List.prod_cons, ← ih, answer,
      conjugate_mul _ (compressDatabases_mul_self k X Y), diagonal_ite_mul_diagonal_ite]
    simp only [List.forall_mem_cons]

/-- In Loewner order, `0 ≤ Acheck - Qcheck ≤ 1 - Kvalid`. Positivity is expressed by
`PosSemidef`, so this statement does not use the entrywise order on matrices. The checked
lists may repeat cells or prescribe conflicting answers. -/
theorem actual_sub_filled_supported_invalid [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    (actualCheck io - filledCheck io).PosSemidef ∧
    (1 - validProjector k X Y -
      (actualCheck io - filledCheck io)).PosSemidef := by
  let C := compressDatabases k X Y
  let a (D : Fin k → Database X Y) : ℂ :=
    if ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 then 1 else 0
  let q (D : Fin k → Database X Y) : ℂ :=
    if ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 then 1 else 0
  let v (D : Fin k → Database X Y) : ℂ :=
    if ∀ j x, D j x ≠ none then 1 else 0
  have hlow : (diagonal (fun D ↦ a D - q D)).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro D
    exact (indicator_bounds _ _ _ (filled_implies_lookup D io)
      (lookup_filled_of_valid D io)).1
  have hupp : (diagonal (fun D ↦ 1 - v D - (a D - q D))).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro D
    exact (indicator_bounds _ _ _ (filled_implies_lookup D io)
      (lookup_filled_of_valid D io)).2
  constructor
  · convert hlow.mul_mul_conjTranspose_same C using 1
    simp only [actualCheck, filledCheck, partialCheck, C, a, q,
      conjTranspose_compressDatabases, ← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  · convert hupp.mul_mul_conjTranspose_same C using 1
    simp only [actualCheck, filledCheck, partialCheck, validProjector, C, a, q, v,
      conjTranspose_compressDatabases, ← diagonal_sub, diagonal_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, compressDatabases_mul_self]

omit [DecidableEq X] in
/-- Flattening oracle indices and addresses preserves the compression matrix. -/
theorem compressDatabases_eq_flat :
    compressDatabases k X Y =
      (compressAll (Fin k × X) Y).submatrix
        (Equiv.curry (Fin k) X (Option Y)).symm
        (Equiv.curry (Fin k) X (Option Y)).symm := by
  ext D D'
  simp only [compressDatabases, compressAll, piKron_apply, submatrix_apply,
    Equiv.curry_symm_apply]
  exact (Fintype.prod_prod_type fun p : Fin k × X ↦
    cellCompress Y (D p.1 p.2) (D' p.1 p.2)).symm

/-- Flattening the private tables preserves the partial-database predicate. -/
theorem partialCheck_eq_flat (io : List ((Fin k × X) × Y)) :
    partialCheck io = (checkProjector Y io).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [partialCheck, checkProjector, submatrix_diagonal_equiv]
  congr 1
  funext D
  simp only [Function.comp_apply, Equiv.curry_symm_apply, Function.uncurry]
  congr 1

/-- The filled check is the same compressed consistency projector under table flattening. -/
theorem filledCheck_eq_flat (io : List ((Fin k × X) × Y)) :
    filledCheck io = (compressedCheckProjector io).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [filledCheck, compressDatabases_eq_flat, partialCheck_eq_flat,
    compressedCheckProjector, submatrix_mul_equiv, submatrix_mul_equiv]

/-- Exact distinct-cell discrepancy for consistent prescriptions over any number of databases.
The constant is the bounds note (26), not the larger constant in the paper's Lemma 9.5. -/
theorem filled_partial_distance_sq [Nonempty Y] (io : List ((Fin k × X) × Y))
    (h : ConsistentIO io) :
    ‖filledCheck io - partialCheck io‖ ^ 2 =
      1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card) := by
  rw [filledCheck_eq_flat, partialCheck_eq_flat]
  change ‖(compressedCheckProjector io - checkProjector Y io).submatrix
    (Equiv.curry (Fin k) X (Option Y)).symm
    (Equiv.curry (Fin k) X (Option Y)).symm‖ ^ 2 = _
  rw [l2_opNorm_submatrix_equiv]
  exact l2_opNorm_compressedCheckProjector_sub_sq h

/-- The filled and partial checkers both vanish for conflicting prescriptions. -/
theorem filled_partial_eq_zero_of_conflict (io : List ((Fin k × X) × Y))
    (h : ¬ ConsistentIO io) : filledCheck io = 0 ∧ partialCheck io = 0 := by
  rw [filledCheck_eq_flat, partialCheck_eq_flat,
    compressedCheckProjector_eq_zero_of_not_consistentIO h,
    checkProjector_eq_zero_of_not_consistentIO h]
  simp

/-- The filled versus partial checker distance is at most `δN` of the number of distinct cells,
including conflicting prescriptions. Repeated equal prescriptions incur no additional cost. -/
theorem filled_partial_distance [Nonempty Y] (io : List ((Fin k × X) × Y)) :
    ‖filledCheck io - partialCheck io‖ ≤
      Real.sqrt (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card)) := by
  by_cases h : ConsistentIO io
  · rw [← filled_partial_distance_sq io h, Real.sqrt_sq (norm_nonneg _)]
  · obtain ⟨hq, hp⟩ := filled_partial_eq_zero_of_conflict io h
    rw [hq, hp, sub_zero, norm_zero]
    exact Real.sqrt_nonneg _

end CompressedReplay
end Quantum
