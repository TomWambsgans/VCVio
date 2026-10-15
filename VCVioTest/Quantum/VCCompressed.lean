/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Compressed
public import VCVio.Quantum.VC.Conditions
public import VCVio.Quantum.MatrixMap.BlockNorm
public import VCVio.CryptoFoundations.MerkleTree.Salted.Extract

/-!
# Tests for the k compressed oracles and the conditions of Theorem 8.4

Checks of the public interface of `VCVio.Quantum.VC.Compressed`, `VCVio.Quantum.VC.Conditions`
and `VCVio.Quantum.MatrixMap.BlockNorm` (ePrint 2025/2166, Lemma 9.2 and Theorem 8.4):

* unitarity and commutation of the ports of two compressed oracles on `Bool → ZMod 2`;
* the law of a one-query adversary against the coherent compressed oracles is the average of its
  laws against the random oracles, and P1 with `κsim = 0` applies to it;
* the norm of an operator controlled by one classical bit is the larger norm of its two blocks;
* the salted Merkle scheme of #858 satisfies the conditions of Theorem 8.4 with `P_good` the
  collision-free databases, so `Quantum.Conditions` is not vacuous.
-/

public section

open Quantum Matrix
open scoped ENNReal Kronecker Matrix.Norms.L2Operator

namespace VCVioTest.QuantumVCCompressed

open EmulatedOracle (cohSpec cohIn)

/-! ## Unitarity and commutation on a small instance -/

/-- Two compressed oracles on `Bool → ZMod 2`. -/
local notation "E₂" => compressedVCOracle 2 Bool (ZMod 2)

/-- Every port of the small instance is unitary. -/
example (i : Fin 2) :
    (E₂).U i ∈ unitaryGroup ((Bool × ZMod 2) × (Fin 2 → Database Bool (ZMod 2))) ℂ :=
  compressedVCOracle_U_mem_unitaryGroup 2 Bool (ZMod 2) i

/-- The private register of the small instance is the pair of databases, started empty. -/
example : (E₂).S = QReg.of (Fin 2 → Database Bool (ZMod 2)) :=
  compressedVCOracle_S 2 Bool (ZMod 2)

/-- The two ports of the small instance commute, on two query registers. -/
example :
    onFactor (slotSnd (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2))) ((E₂).U 0) *
        onFactor (slotFst (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
          ((E₂).U 1) =
      onFactor (slotFst (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
          ((E₂).U 1) *
        onFactor (slotSnd (Bool × ZMod 2) (Bool × ZMod 2) (Fin 2 → Database Bool (ZMod 2)))
          ((E₂).U 0) :=
  compressedVCOracle_commute 0 1

/-- The small instance satisfies the oracle commutation of Definition 7.3. -/
example : OraclesCommute E₂ :=
  oraclesCommute_compressedVCOracle

/-! ## P1 on a one-query adversary -/

/-- The register of a one-query adversary: the coherent query register and nothing beside it. -/
local notation "Reg" => QReg.of (cohIn (oIn 2 Bool (ZMod 2)) × Unit)

/-- One coherent call of the two oracles. -/
noncomputable def oneQuery :=
  QuantumComp.query (L := LocalSig.instruments.{0}) (spec := cohSpec (oIn 2 Bool (ZMod 2)))
    (A := Reg) () (QReg.of Unit) (Equiv.refl _)

/-- The adversary makes one call. -/
theorem isQueryBound_oneQuery : oneQuery.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos

/-- **The law of the one-query adversary** against the coherent compressed oracles is the average
of its laws against the coherent random oracles `H : Fin 2 → Bool → ZMod 2`, for any input state
and any observation of its output. -/
example (ρ : SubState Reg) {γ : Type} [MeasurableSpace γ]
    (f : (Σ u, (fun u ↦ PSigma fun _ : u = QReg.of ((cohSpec (oIn 2 Bool (ZMod 2))).Out () ×
      QReg.of Unit) ↦ (cohSpec (oIn 2 Bool (ZMod 2))).Result ()) u) → γ) :
    (E₂).coherent.toRuntime.outcomeLawWith .instruments oneQuery ρ f =
      ∑ H : Fin 2 → Bool → ZMod 2, (Fintype.card (Fin 2 → Bool → ZMod 2) : ℝ≥0∞)⁻¹ •
        (romVCOracle 2 Bool (ZMod 2) H).coherent.toRuntime.outcomeLawWith .instruments oneQuery
          ρ f :=
  outcomeLawWith_coherent_compressedVCOracle _ _ _ _

/-- There are `2 ^ 4 = 16` random oracles in the average. -/
example : Fintype.card (Fin 2 → Bool → ZMod 2) = 16 := by
  simp [ZMod.card]

/-- **P1 with `κsim = 0` on the one-query adversary**: its probability of accepting against the
coherent compressed oracles is at most the averaged probability against the random oracles. -/
example (ρ : SubState Reg) (f : (Σ u, (fun u ↦ PSigma fun _ : u =
      QReg.of ((cohSpec (oIn 2 Bool (ZMod 2))).Out () × QReg.of Unit) ↦
        (cohSpec (oIn 2 Bool (ZMod 2))).Result ()) u) → Bool) :
    (E₂).coherent.toRuntime.outcomeLawWith .instruments oneQuery ρ f {true} ≤
      mixedLawWith
        (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin 2 → Bool → ZMod 2))
        (fun H ↦ (romVCOracle 2 Bool (ZMod 2) H).coherent.toRuntime) .instruments oneQuery ρ
        (fun _ ↦ f) {true} + 0 :=
  (simulates_compressedVCOracle 1 oneQuery f ρ isQueryBound_oneQuery).1

/-! ## The norm of a classically controlled operator with two blocks -/

/-- **Two blocks.** The operator `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ B` controlled by one bit has norm
`max ‖A‖ ‖B‖`. -/
example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℂ) :
    ‖single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ⊗ₖ A + single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ⊗ₖ B‖ =
      max ‖A‖ ‖B‖ := by
  have h := l2_opNorm_sum_single_kronecker (𝕜 := ℂ) ![A, B]
  rw [Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  have hbdd : BddAbove (Set.range fun c ↦ ‖(![A, B] : Fin 2 → Matrix m n ℂ) c‖) :=
    (Set.finite_range _).bddAbove
  refine le_antisymm (ciSup_le fun c ↦ ?_) (max_le ?_ ?_)
  · fin_cases c
    · exact le_max_left _ _
    · exact le_max_right _ _
  · simpa using le_ciSup hbdd 0
  · simpa using le_ciSup hbdd 1

/-! ## Non-vacuity: the salted Merkle scheme satisfies the conditions -/

section Merkle

open SaltedMerkle OracleComp

variable {X Y Msg Salt : Type} [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt] [SampleableType Salt]

/-- **The salted Merkle scheme satisfies the conditions of Theorem 8.4** (ePrint 2025/2166, §8.3,
l.3135–3151): `MTMultiExtract` with the collision-free databases as `P_good` and the trees of
depths `d i`. Condition 1 is `SaltedMerkle.checkIOForm`; the opening is deterministic, so the
support conditions reduce to the deterministic binding and validity of `MTMultiExtract`. -/
theorem merkle_conditions (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ) :
    Conditions (fun i ↦ (scheme (Msg := Msg) enc (d i)).toVectorCommitment)
      (fun i ↦ checkIOForm enc (d i)) (multiExtract enc d) (fun _ ↦ tdBot) collisionFree where
  admissible := multiExtract_admissible enc d
  empty_mem := empty_mem_collisionFree
  binding hk idx hidx cm ans pf Ds hD h i := by
    have hb := multiExtract_binding enc d hk idx hidx cm ans pf Ds hD h i
    refine ⟨hb.1, fun pf' hpf' ↦ ?_⟩
    rw [← hb.2]
    exact eq_of_mem_support_pure hpf'
  valid hk idx hidx cm Ds i pf hpf := by
    rw [eq_of_mem_support_pure hpf]
    exact multiExtract_valid enc d hk idx hidx cm Ds i

/-- The query counts of the salted Merkle scheme: a check of `q` positions in a tree of depth
`d i` makes `q * (d i + 1)` queries, so `q2` is the largest `2 ^ d i * (d i + 1)`. -/
example (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ) (i : Fin k) :
    2 ^ d i * (d i + 1) ≤ q2 (VC := fun i ↦ (scheme (Msg := Msg) enc (d i)).toVectorCommitment)
      (fun i ↦ checkIOForm enc (d i)) :=
  qVC_le_q2 (fun i ↦ checkIOForm enc (d i)) i

/-- `q1` of the salted Merkle scheme is at least the count of a single check of the whole
budget. -/
example (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ) (i : Fin k) (qs : ℕ) :
    qs * (d i + 1) ≤ q1 (VC := fun i ↦ (scheme (Msg := Msg) enc (d i)).toVectorCommitment)
      (fun i ↦ checkIOForm enc (d i)) qs := by
  have h := sum_qVC_le_q1 (fun i ↦ checkIOForm enc (d i)) (qs := qs) (Pi.single i qs)
    (by simp)
  refine le_trans ?_ h
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj, checkIOForm]) (by simp)]
  simp [checkIOForm]

/-- The offline label of the salted Merkle scheme marks the collision-free databases. -/
example [Fintype X] [DecidablePred (· ∈ (collisionFree : Set (Database X Y)))]
    (D : Database X Y) : offlineLabel collisionFree D = true ↔ D ∈ collisionFree :=
  offlineLabel_eq_true_iff _ D

end Merkle

end VCVioTest.QuantumVCCompressed
