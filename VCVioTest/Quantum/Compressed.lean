/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Action
public import VCVio.Quantum.Oracle.Compressed.Measurement
public import VCVio.Quantum.Oracle.Compressed.Truncation
public import VCVioTest.Quantum.Oracle

/-!
# Compressed-oracle regression tests

Functions `Fin 2 → Fin 2`, queried on the register `Fin 2 × Fin 2`.

* The one-cell compression on `ℂ^(Option (Fin 2)) ≅ ℂ³`, written out as a `3 × 3` matrix in the
  basis `|⊥⟩, |0⟩, |1⟩`.
* One query of `|x, 0⟩` against the empty database `|⊥, ⊥⟩`, by the one-cell formula.
* Deutsch's algorithm, as a program, has the same law against the compressed runtime as in the
  quantum random-oracle model.
* **An adaptive program** calls the oracle, measures the response bit, and on `1` calls again.
  It makes at most two calls on every path. Its law against the compressed runtime, against the
  runtime truncated at two cells, and after the database is measured, is the law of the quantum
  random-oracle model; it ends with at most two nonempty cells.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ENNReal

namespace VCVioTest.QuantumCompressed

open VCVioTest.QuantumOracle

/-! ## The one-cell compression on `ℂ³` -/

/-- The one-cell compression for `Y = Fin 2` in the basis `|⊥⟩, |0⟩, |1⟩`. -/
example :
    (cellCompress (Fin 2)).submatrix ![none, some 0, some 1] ![none, some 0, some 1] =
      (!![0, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ);
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), 1 / 2, -1 / 2;
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), -1 / 2, 1 / 2] : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cellAmp]

/-- The one-cell compression for `Y = Fin 2` is an involution. -/
example : cellCompress (Fin 2) * cellCompress (Fin 2) = 1 :=
  cellCompress_mul_self (Fin 2)

/-! ## One query against the empty database -/

/-- One query of `|x, 0⟩` against the empty database: with `c = 2^(-1/2)`,
`cO |x, 0⟩|⊥, ⊥⟩ = ∑ v, (½ |x, v⟩|⊥, ⊥⟩ + ∑ v'', (δ v'' v - ½) c |x, v⟩|D[x ↦ v'']⟩)`. -/
example (x : Fin 2) :
    compressedOracle (Fin 2) (Fin 2) *ᵥ Pi.single ((x, 0), Database.empty) 1 =
      ∑ v : Fin 2, ((2 : ℂ)⁻¹ • Pi.single ((x, v), Database.empty) 1 +
        ∑ v'' : Fin 2, (((if v'' = v then 1 else 0) - (2 : ℂ)⁻¹) * ((Real.sqrt 2)⁻¹ : ℝ)) •
          Pi.single ((x, v), Function.update Database.empty x (some v'')) 1) := by
  rw [compressedOracle_mulVec_single_of_eq_none 0 rfl]
  simp [cellAmp]

/-! ## Deutsch's algorithm against the compressed runtime -/

/-- Deutsch's algorithm, as a program, has the same law against the compressed runtime as in the
quantum random-oracle model. -/
example :
    (compressedRuntime (Fin 2) (Fin 2)).outcomeLaw₂ .instruments deutschComp deutsch.init =
      qromLaw₂ .instruments deutschComp deutsch.init :=
  outcomeLaw₂_compressedRuntime _ _ _

/-! ## An adaptive program -/

/-- One call on the whole register `Fin 2 × Fin 2`, with the trivial remainder. -/
noncomputable def callReg : QComp qrom2 (QReg.of Reg) (QReg.of Reg) Unit :=
  (QuantumComp₂.query (L := LocalSig.instruments) () (QReg.of Unit)
      (Equiv.prodPUnit Reg).symm).bind fun _ ↦
    QComp.act (B := QReg.of Reg) (SubInstrument.relabel (Equiv.prodPUnit Reg))

theorem isQueryBound_callReg : callReg.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp₂.isQueryBound_bind
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos)
      fun _ ↦ QComp.isQueryBound_act _ 0).mono fun _ ↦ by simp

/-- Call the oracle, measure the response bit, and on `1` call the oracle again; return the bit.
The second call depends on the measured result of the first. -/
noncomputable def queryMeasureQuery : QComp qrom2 (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  callReg.bind fun _ ↦
    (QComp.act (A := QReg.of Reg) (B := QReg.of Reg)
        (SubInstrument.classical id fun m : Reg ↦ m.2)).bind fun b ↦
      if b = 1 then callReg.bind fun _ ↦ QuantumComp₂.pure b else QuantumComp₂.pure b

/-- The adaptive program makes at most two calls on every path. -/
theorem isQueryBound_queryMeasureQuery : queryMeasureQuery.IsQueryBound fun _ ↦ 2 := by
  refine (QuantumComp₂.isQueryBound_bind (b₂ := fun _ ↦ 1) isQueryBound_callReg fun _ ↦ ?_).mono
    fun _ ↦ le_rfl
  rw [QComp.isQueryBound_act_bind_iff]
  intro b
  split_ifs
  · exact (QuantumComp₂.isQueryBound_bind (b₂ := 0) isQueryBound_callReg
      fun _ ↦ QuantumComp₂.isQueryBound_pure _ _).mono fun _ ↦ by simp
  · exact QuantumComp₂.isQueryBound_pure _ _

/-- Against the compressed runtime, the adaptive program has the law of the quantum random-oracle
model. -/
example (ρ : SubState (QReg.of Reg)) :
    (compressedRuntime (Fin 2) (Fin 2)).outcomeLaw₂ .instruments queryMeasureQuery ρ =
      qromLaw₂ .instruments queryMeasureQuery ρ :=
  outcomeLaw₂_compressedRuntime _ _ _

/-- The adaptive program ends with at most two nonempty cells. -/
example (ρ : SubState (QReg.of Reg)) (b : Fin 2) :
    DatabaseSupportedOn 2
      ((compressedRuntime (Fin 2) (Fin 2)).jointPost₂ .instruments queryMeasureQuery ρ b).matrix :=
  databaseSupportedOn_jointPost_compressedRuntime (W := QuantumComp₂.Leaf (QReg.of Reg) (Fin 2))
    _ isQueryBound_queryMeasureQuery _ _

/-- Truncating the database at two cells does not change the law of the adaptive program
(Lemma 4.4 of ePrint 2025/2166). -/
example (ρ : SubState (QReg.of Reg)) :
    (truncatedRuntime (Fin 2) (Fin 2) 2).outcomeLaw₂ .instruments queryMeasureQuery ρ =
      qromLaw₂ .instruments queryMeasureQuery ρ :=
  outcomeLaw₂_truncatedRuntime_eq_qromLaw₂ _ isQueryBound_queryMeasureQuery le_rfl _

/-- Measuring the database after the adaptive program leaves the law of its value unchanged. -/
example [MeasurableSpace (Database (Fin 2) (Fin 2))] (ρ : SubState (QReg.of Reg)) :
    (compressedJointLaw .instruments queryMeasureQuery ρ).map Prod.fst =
      qromLaw₂ .instruments queryMeasureQuery ρ :=
  map_fst_compressedJointLaw_eq_qromLaw _ _ _

end VCVioTest.QuantumCompressed
