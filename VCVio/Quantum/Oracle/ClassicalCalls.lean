/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Oracle.Emulated

/-!
# Coins, sequencing and basis calls for experiments

Helpers for running randomized classical algorithms from inside a quantum experiment, as the
challengers of the security experiments of ePrint 2025/2166 (§7, l.2866–2905) do.

* **Coins.** `Quantum.SubInstrument.uniform Ω A` draws a uniform outcome in `Ω` and leaves the
  register `A` untouched; its branch at every outcome is the map `ρ ↦ ρ / |Ω|`. It is the
  measurement of a fresh uniform register, and answers the queries of `unifSpec` through
  `Quantum.QComp.coinImpl`, so a `ProbComp` or an `OracleComp (unifSpec + _)` runs inside an
  experiment by `OracleComp.toQuantumAt`.
* **Sequencing.** `Quantum.QComp.pi f` runs the programs `f 0, …, f (k - 1)` in order on a held
  register and returns the dependent tuple of their results.
* **Basis calls against an emulated oracle.** The branch of `Quantum.QComp.callBasis` at a
  reading is the sum, over the port outputs giving that reading, of the Kraus map of
  `1_B ⊗ ⟨o|U_p|a⟩` (`Quantum.EmulatedOracle.branch_run₂_callBasis`).

## Main definitions

* `Quantum.SubInstrument.uniform`, `Quantum.QComp.coinImpl`, `Quantum.QComp.pi`,
  `Quantum.EmulatedOracle.block`.

## Main results

* `Quantum.SubInstrument.branch_uniform_apply`, `Quantum.SubInstrument.lossless_uniform`.
* `Quantum.QComp.lossless_pi`, `Quantum.QComp.isQueryBound_pi`.
* `Quantum.EmulatedOracle.branch_run₂_callBasis`.
-/

public section

open Matrix OracleSpec
open scoped Kronecker

universe u u₁ v₁ w

namespace Quantum

/-! ## Uniform coins -/

namespace SubInstrument

variable (Ω : Type*) [Fintype Ω] [Nonempty Ω] (A : Type*) [Fintype A] [DecidableEq A]

/-- The Kraus operator of every outcome of a uniform coin: `|Ω|^(-1/2) • 1`. -/
@[expose]
noncomputable def uniformKraus : Matrix A A ℂ :=
  ((Real.sqrt (Fintype.card Ω : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix A A ℂ)

omit [Nonempty Ω] in
private theorem sqrt_inv_card_mul_self : (((Real.sqrt (Fintype.card Ω : ℝ)⁻¹ : ℝ) : ℂ)) *
    ((Real.sqrt (Fintype.card Ω : ℝ)⁻¹ : ℝ) : ℂ) = (Fintype.card Ω : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simp

omit [Nonempty Ω] in
/-- The Kraus operator of a uniform coin, composed with its adjoint, is `|Ω|⁻¹ • 1`. -/
theorem conjTranspose_uniformKraus_mul_self :
    (uniformKraus Ω A)ᴴ * uniformKraus Ω A = ((Fintype.card Ω : ℂ)⁻¹) • (1 : Matrix A A ℂ) := by
  simp only [uniformKraus, conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal, smul_mul_smul, Matrix.mul_one, sqrt_inv_card_mul_self]

/-- The Kraus operators of a uniform coin form a complete family. -/
theorem sum_conjTranspose_uniformKraus_mul_self :
    ∑ _ω : Ω, (uniformKraus Ω A)ᴴ * uniformKraus Ω A = 1 := by
  rw [conjTranspose_uniformKraus_mul_self, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

/-- **A uniform coin**: draw a uniform outcome in `Ω` and leave the register `A` untouched. Each
branch is `ρ ↦ ρ / |Ω|` (`Quantum.SubInstrument.branch_uniform_apply`). It is the measurement of
a fresh register prepared in the uniform state, with the measured register discarded. -/
@[expose]
noncomputable def uniform : SubInstrument A A Ω :=
  ofKraus (fun _ ↦ uniformKraus Ω A) (sum_conjTranspose_uniformKraus_mul_self Ω A)

/-- Each branch of a uniform coin scales the state by `1 / |Ω|`. -/
theorem branch_uniform_apply (ω : Ω) (ρ : Matrix A A ℂ) :
    (uniform Ω A).branch ω ρ = ((Fintype.card Ω : ℂ)⁻¹) • ρ := by
  rw [uniform, branch_ofKraus_apply, MatrixMap.conj_apply]
  simp only [uniformKraus, conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal, smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    sqrt_inv_card_mul_self]

/-- A uniform coin is lossless. -/
theorem lossless_uniform : (uniform Ω A).Lossless :=
  lossless_ofKraus _ _

end SubInstrument

/-! ## Coins and sequencing in programs -/

namespace QComp

variable {spec : QuantumOracleSpec.{u₁, v₁}} {B : QReg}

/-- **Coins inside an experiment.** The query `n` of `unifSpec` (a uniform element of
`Fin (n + 1)`) is answered by a uniform coin that leaves the held register `B` untouched. -/
@[expose]
noncomputable def coinImpl (spec : QuantumOracleSpec.{u₁, v₁}) (B : QReg) :
    QueryImpl unifSpec (QComp.{u₁, v₁, 0} spec B B) :=
  fun n ↦ QComp.act (SubInstrument.uniform (Fin (n + 1)) B)

/-- Coins are lossless. -/
theorem lossless_coinImpl (n : ℕ) : (coinImpl spec B n).Lossless .instruments :=
  QComp.lossless_act (SubInstrument.lossless_uniform _ _)

/-- Coins make no call. -/
theorem isQueryBound_coinImpl (n : ℕ) (b : spec.Port → ℕ) : (coinImpl spec B n).IsQueryBound b :=
  QComp.isQueryBound_act _ b

/-- **Sequencing over `Fin k`.** Run `f 0, …, f (k - 1)` in order on the held register and
return the dependent tuple of their results. -/
@[expose]
noncomputable def pi : {k : ℕ} → {β : Fin k → Type w} → ((i : Fin k) → QComp spec B B (β i)) →
    QComp spec B B ((i : Fin k) → β i)
  | 0, _, _ => QuantumComp₂.pure fun i ↦ i.elim0
  | _ + 1, _, f => (f 0).bind fun b ↦ (pi fun i ↦ f i.succ).bind fun bs ↦
      QuantumComp₂.pure (Fin.cons b bs)

/-- Sequencing lossless programs is lossless. -/
theorem lossless_pi : {k : ℕ} → {β : Fin k → Type w} → {f : (i : Fin k) → QComp spec B B (β i)} →
    (∀ i, (f i).Lossless .instruments) → (pi f).Lossless .instruments
  | 0, _, _, _ => QuantumComp₂.lossless_pure _
  | _ + 1, _, _, hf => QuantumComp₂.lossless_bind (hf 0) fun _ ↦
      QuantumComp₂.lossless_bind (lossless_pi fun i ↦ hf i.succ) fun _ ↦
        QuantumComp₂.lossless_pure _

/-- The sequence of the programs `f i` is within the sum of their budgets. -/
theorem isQueryBound_pi : {k : ℕ} → {β : Fin k → Type w} →
    {f : (i : Fin k) → QComp spec B B (β i)} → {b : Fin k → spec.Port → ℕ} →
    (∀ i, (f i).IsQueryBound (b i)) → (pi f).IsQueryBound (∑ i, b i)
  | 0, _, _, _, _ => QuantumComp₂.isQueryBound_pure _ _
  | _ + 1, _, _, b, hf => by
    rw [Fin.sum_univ_succ, ← add_zero (∑ i : Fin _, b i.succ)]
    exact QuantumComp₂.isQueryBound_bind (hf 0) fun _ ↦
      QuantumComp₂.isQueryBound_bind (isQueryBound_pi fun i ↦ hf i.succ) fun _ ↦
        QuantumComp₂.isQueryBound_pure _ _

end QComp

/-! ## Basis calls against an emulated oracle -/

namespace EmulatedOracle

variable {P : Type u} {In : P → QReg} (E : EmulatedOracle P In)

/-- The block `⟨o|U_p|a⟩` of the unitary of port `p` on the private register. -/
@[expose]
noncomputable def block (p : P) (o a : In p) : Matrix E.S E.S ℂ :=
  (E.U p).submatrix (fun d ↦ (o, d)) fun d ↦ (a, d)

/-- The entries of a block. -/
@[simp]
theorem block_apply (p : P) (o a : In p) (d d' : E.S) : E.block p o a d d' = E.U p (o, d) (a, d') :=
  rfl

/-- **The branch of a basis call against an emulated oracle**: at the reading `c`, the sum over
the port outputs `o` with `read o () = c` of the Kraus map of `1_B ⊗ ⟨o|U_p|a⟩`. The held
register `B` is untouched, and the private register is acted on by a block of the port's
unitary. -/
theorem branch_run₂_callBasis {β : Type} [DecidableEq β] (p : P) (B : QReg) (a : In p)
    (read : In p → Unit → β) (c : β) :
    (E.toRuntime.run₂ .instruments
      (QComp.callBasis (spec := uSpec P In) p B a read)).branch c =
      ∑ o, if read o () = c then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ E.block p o a)
        else 0 := by
  rw [QComp.run₂_callBasis, SubInstrument.branch_bind_unit, SubInstrument.branch_bind_unit,
    SubInstrument.bind_pure, E.toRuntime.queryStep_branch_eq_conj (M := E.U p) rfl]
  simp only [QComp.callBasisPrep, QComp.callBasisMeasure, SubInstrument.branch_bind_unit,
    SubInstrument.branch_bind_bind_unit_pure, SubInstrument.classical,
    SubInstrument.branch_map_apply_univ, SubInstrument.branch_frame_apply,
    SubInstrument.branch_ofKraus_apply, SubInstrument.branch_relabel, ite_true,
    Fintype.sum_unique, ← Finset.sum_filter, MatrixMap.amplify_sum, MatrixMap.amplify_comp,
    MatrixMap.amplify_conj, ← MatrixMap.conj_mul]
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  simp only [← LinearMap.comp_apply, ← MatrixMap.conj_mul]
  refine congrArg (MatrixMap.conj · ρ) ?_
  have hR : ((single a () (1 : ℂ) ⊗ₖ (1 : Matrix B B ℂ)) *
      basisMatrix (Equiv.uniqueProd B Unit).symm) ⊗ₖ (1 : Matrix E.S E.S ℂ) =
      basisMatrix fun x : B × E.S ↦ ((a, x.1), x.2) := by
    ext ⟨⟨i, b⟩, d⟩ ⟨b', d'⟩
    simp only [kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_prod_type, basisMatrix_apply]
    split_ifs <;> simp_all
  have hL : (basisMatrix (Equiv.uniqueProd B Unit) ⊗ₖ (1 : Matrix E.S E.S ℂ)) *
      ((single () o (1 : ℂ) ⊗ₖ (1 : Matrix B B ℂ)) ⊗ₖ (1 : Matrix E.S E.S ℂ)) =
      (basisMatrix fun x : B × E.S ↦ ((o, x.1), x.2))ᴴ := by
    ext ⟨b, d⟩ ⟨⟨i, b'⟩, d'⟩
    simp only [kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_prod_type, basisMatrix_apply, conjTranspose_apply]
    split_ifs <;> first | (simp_all; done) | (simp_all; tauto)
  rw [hR, ← Matrix.mul_assoc, hL]
  simp only [Matrix.mul_assoc]
  rw [← basisMatrix_comp, basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut _ _ _),
    ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← basisMatrix_comp, ← Matrix.mul_assoc,
    conjTranspose_basisMatrix_mul_mul_basisMatrix]
  ext ⟨b, d⟩ ⟨b', d'⟩
  simp [block, QuantumRuntime.queryEquivOut, Matrix.one_apply]

end EmulatedOracle

end Quantum
