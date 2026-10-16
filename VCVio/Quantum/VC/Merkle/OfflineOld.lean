/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerComparison
public import VCVio.Quantum.Comp.Potential
public import VCVio.Quantum.MatrixMap.Commutant
public import VCVio.CryptoFoundations.MerkleTree.Salted.Instability

/-!
# Concatenated extraction responses and the old-oracle error

`oldOfflineError` is the real-valued function `F` of the repair note FIX (35), with
`oldMerkleOfflineError` converting opened positions to `qs * (d + 1)` raw checks.
The leakage polynomial and invalid-sector term are those of FIX (26b).
Natural subtractions are truncated before casting, and division by six is real division.
Physical parameters have `N > 0` and nonnegative ordinary and extraction masses.

`databasePopulation_post_old` bounds total populated cells in every original post-adversary
branch of the old coherent ordinary/extraction runtime. It applies to any extractor and code,
and general local operations with register-changing leaves. Its proof lifts the one-cell growth
property structurally through the program; it does not require positivity of intermediate matrices.

`TpDCode.concat` encodes each decommitment in a separate additive coordinate, with a separate
length coordinate. Its coherent extraction matrix factors into commuting translations for any
partition of the response positions. For full Merkle tuples each part depends only on its
selected databases; duplicate-index tuples have database-independent parts. The generic
`checker_batches_factor` records the algebraic rearrangement of FIX (26b).

`filledCell_extraction_commutator_le` proves the local estimate in FIX (27), uniformly over
ancilla unitaries and every function of an extraction result, including component batches.
`invalidStack` represents the sum of invalid weights as a rectangular trace potential,
and `actual_sub_filled_potential_le` bounds the checker error by that potential on arbitrary
entangled mixed states. `rpow_inv_two_tsum_conj_unitary_le` supplies the direct-sum
triangle inequality without requiring the observables to sum to a projector.
The local commutator estimate uses the exact distance from the uniform projector to its
normalized restriction to
unchanged labels. The summed population-restricted estimate remains a separate obligation.

The leakage polynomial is the exact prefix sum in FIX (28). Its Cauchy--Schwarz estimate is
stated in `ℝ≥0∞`, including infinite masses. This module does not assert `OfflineExtractable`:
the reachable invalid-norm estimate and its transfer to the actual challenger remain necessary.
No assertion that arbitrary classical checks preserve population is used. The coefficients
four and eight in FIX (36) belong to the downstream reduction, not to this P4 error function.
-/

public section

open scoped ENNReal Kronecker Matrix.Norms.L2Operator ComplexOrder

open Matrix

universe u v w

namespace Quantum

/-! ## Local invalid-sector commutators -/

section uniformProjector

variable {Y : Type*} [DecidableEq Y]

private def subsetVector (s : Finset Y) : Y → ℂ := fun y ↦ if y ∈ s then 1 else 0

/-- The orthogonal projector onto the uniform vector on a subset, or zero for the empty subset. -/
noncomputable def uniformSubsetProjector (s : Finset Y) : Matrix Y Y ℂ :=
  (s.card : ℂ)⁻¹ • vecMulVec (subsetVector s) (subsetVector s)

private theorem subsetVector_star (s : Finset Y) : star (subsetVector s) = subsetVector s := by
  ext y
  simp [subsetVector]

/-- The uniform subset projector is Hermitian. -/
theorem uniformSubsetProjector_hermitian (s : Finset Y) :
    (uniformSubsetProjector s)ᴴ = uniformSubsetProjector s := by
  simp [uniformSubsetProjector, subsetVector_star]

variable [Fintype Y]

private theorem subsetVector_dot (s t : Finset Y) :
    subsetVector s ⬝ᵥ subsetVector t = ((s ∩ t).card : ℂ) := by
  classical
  calc
    _ = ∑ y : Y, if y ∈ s ∩ t then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [subsetVector, Finset.mem_inter]
      split_ifs <;> simp_all
    _ = _ := by
      rw [Finset.sum_boole]
      congr 2
      ext y
      simp

/-- Multiplication of two uniform subset projectors. -/
private theorem uniformSubsetProjector_mul (s t : Finset Y) :
    uniformSubsetProjector s * uniformSubsetProjector t =
      ((s.card : ℂ)⁻¹ * (t.card : ℂ)⁻¹ * (s ∩ t).card) •
        vecMulVec (subsetVector s) (subsetVector t) := by
  simp only [uniformSubsetProjector, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    subsetVector_dot, vecMulVec_smul, smul_smul]
  congr 1
  ring

/-- Uniform subset projectors are idempotent, including the empty subset. -/
theorem uniformSubsetProjector_idempotent (s : Finset Y) :
    uniformSubsetProjector s * uniformSubsetProjector s = uniformSubsetProjector s := by
  rw [uniformSubsetProjector_mul, Finset.inter_self, uniformSubsetProjector]
  congr 1
  by_cases hs : (s.card : ℂ) = 0
  · simp [hs]
  · field_simp

/-- Sandwiching a uniform subset projector by the whole-space uniform projector. -/
theorem uniformSubsetProjector_sandwich_univ (s : Finset Y) :
    uniformSubsetProjector Finset.univ * uniformSubsetProjector s *
        uniformSubsetProjector Finset.univ =
      ((s.card : ℂ) / Fintype.card Y) • uniformSubsetProjector Finset.univ := by
  simp only [uniformSubsetProjector, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, subsetVector_dot, Finset.univ_inter,
    Finset.inter_univ, smul_smul, Finset.card_univ]
  congr 1
  by_cases hs : (s.card : ℂ) = 0
  · simp [hs]
  · field_simp

/-- Sandwiching the whole-space uniform projector by a subset projector. -/
theorem uniformSubsetProjector_univ_sandwich (s : Finset Y) :
    uniformSubsetProjector s * uniformSubsetProjector Finset.univ * uniformSubsetProjector s =
      ((s.card : ℂ) / Fintype.card Y) • uniformSubsetProjector s := by
  simp only [uniformSubsetProjector, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, subsetVector_dot, Finset.univ_inter,
    Finset.inter_univ, smul_smul, Finset.card_univ]
  congr 1
  by_cases hs : (s.card : ℂ) = 0
  · simp [hs]
  · field_simp

/-- The distance to a uniform subset projector is the square root of the omitted fraction,
including the empty subset. -/
theorem uniformSubsetProjector_distance_sq [Nonempty Y] (s : Finset Y) :
    ‖uniformSubsetProjector Finset.univ - uniformSubsetProjector s‖ ^ 2 =
      1 - (s.card : ℝ) / Fintype.card Y := by
  apply l2_opNorm_sub_sq_eq_one_sub_of_mul_mul_eq
    (uniformSubsetProjector_hermitian _) (uniformSubsetProjector_idempotent _)
    (uniformSubsetProjector_hermitian _) (uniformSubsetProjector_idempotent _)
  · exact (div_le_one (by positivity)).mpr (by exact_mod_cast Finset.card_le_univ s)
  · simpa using uniformSubsetProjector_sandwich_univ s
  · simpa using uniformSubsetProjector_univ_sandwich s
  · intro h
    obtain ⟨y⟩ := ‹Nonempty Y›
    have hh := congrArg (fun M : Matrix Y Y ℂ ↦ M y y) h
    have hN : (Fintype.card Y : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [uniformSubsetProjector, vecMulVec_apply, subsetVector, hN] at hh

omit [Fintype Y] in
/-- A subset of one label class gives a label-preserving uniform projector. -/
theorem uniformSubsetProjector_pinch {κ : Type*} [DecidableEq κ] (β : Y → κ)
    (s : Finset Y) (h : ∀ a ∈ s, ∀ b ∈ s, β a = β b) :
    pinch β (uniformSubsetProjector s) = uniformSubsetProjector s := by
  apply pinch_eq_self_iff.mpr
  intro a b hab
  have ha : a ∈ s := by
    by_contra ha
    exact hab (by simp [uniformSubsetProjector, vecMulVec_apply, subsetVector, ha])
  have hb : b ∈ s := by
    by_contra hb
    exact hab (by simp [uniformSubsetProjector, vecMulVec_apply, subsetVector, hb])
  exact h a ha b hb

/-- A coherent label-controlled operation has uniform-projector commutator at most twice
the square root of the fraction outside any one label class, with an arbitrary ancilla.
This is the single filled-cell estimate used in the repair note FIX (27). -/
theorem uniformSubsetProjector_commutator_le [Nonempty Y]
    {κ Z : Type*} [Fintype Z] [DecidableEq Z]
    (β : Y → κ) (s : Finset Y) (hs : ∀ a ∈ s, ∀ b ∈ s, β a = β b)
    (U : κ → Matrix Z Z ℂ) (hU : ∀ k, U k ∈ unitaryGroup Z ℂ) :
    ‖labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k) *
        (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) *
        labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)‖ ≤
      2 * Real.sqrt (1 - (s.card : ℝ) / Fintype.card Y) := by
  classical
  have hh := l2_opNorm_commutator_labelControlled_one_kronecker_le
    (uniformSubsetProjector_pinch β s hs) hU
    (A := uniformSubsetProjector Finset.univ)
  have hd : ‖uniformSubsetProjector Finset.univ - uniformSubsetProjector s‖ =
      Real.sqrt (1 - (s.card : ℝ) / Fintype.card Y) := by
    rw [← uniformSubsetProjector_distance_sq s, Real.sqrt_sq (norm_nonneg _)]
  rwa [hd] at hh

/-- On the filled labels, the compressed empty-sector projector is the uniform projector.
This identifies the single-cell operator in FIX (27) with the old oracle's invalid sector. -/
theorem uniformSubsetProjector_univ_eq_cellInvalid :
    uniformSubsetProjector (Finset.univ : Finset Y) =
      (cellCompress Y * diagonal (fun a : Option Y ↦ if a = none then 1 else 0) *
        cellCompress Y).submatrix some some := by
  ext a b
  simp [uniformSubsetProjector, subsetVector, vecMulVec_apply, Matrix.mul_apply,
    submatrix_apply, diagonal_apply, cellAmp_mul_self]

/-- Counting changed labels bounds the coherent uniform-projector commutator. The comparison
label may be the extraction result on the absent cell. -/
theorem uniformProjector_commutator_le [Nonempty Y]
    {κ Z : Type*} [DecidableEq κ] [Fintype Z] [DecidableEq Z]
    (β : Y → κ) (baseline : κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ k, U k ∈ unitaryGroup Z ℂ) :
    ‖labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k) *
        (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) *
        labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)‖ ≤
      2 * Real.sqrt ((Finset.univ.filter fun y ↦ β y ≠ baseline).card /
        (Fintype.card Y : ℝ)) := by
  have hh := uniformSubsetProjector_commutator_le β
    (Finset.univ.filter fun y ↦ β y = baseline)
    (fun a ha b hb ↦ (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) U hU
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y ↦ β y = baseline)
  have hc' : ((Finset.univ.filter fun y ↦ β y = baseline).card : ℝ) +
      (Finset.univ.filter fun y ↦ β y ≠ baseline).card = Fintype.card Y := by
    exact_mod_cast hc
  have he : 1 - ((Finset.univ.filter fun y ↦ β y = baseline).card : ℝ) / Fintype.card Y =
      (Finset.univ.filter fun y ↦ β y ≠ baseline).card / (Fintype.card Y : ℝ) := by
    apply (sub_eq_iff_eq_add).mpr
    rw [← add_div, add_comm, hc', div_self (by positivity)]
  rwa [he] at hh

end uniformProjector

namespace MatrixMap

/-- A unitary changes a family of observable seminorms by at most its commutator seminorm.
The family need not sum to a projector, and the positive input need not have trace one.
This is the direct-sum triangle step in FIX (27)–(28). -/
theorem rpow_inv_two_tsum_conj_unitary_le
    {C S : Type*} [Fintype S] [DecidableEq S] (R : C → Matrix S S ℂ)
    (U : Matrix S S ℂ) (hU : Uᴴ * U = 1) {ρ : Matrix S S ℂ} (hρ : ρ.PosSemidef) :
    (∑' c, ENNReal.ofReal (conj (R c) (conj U ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' c, ENNReal.ofReal (conj (R c) ρ).trace.re) ^ (2⁻¹ : ℝ) +
      (∑' c, ENNReal.ofReal (conj (R c * U - U * R c) ρ).trace.re) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_tsum_le_of_le_add
  intro c
  have he : U * R c + (R c * U - U * R c) = R c * U := by abel
  have ht : (conj (U * R c) ρ).trace = (conj (R c) ρ).trace := by
    rw [trace_conj_apply, trace_conj_apply, conjTranspose_mul]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hh := ofReal_trace_conj_add_rpow_le hρ (U * R c) (R c * U - U * R c)
  rw [he, ht, conj_mul, LinearMap.comp_apply] at hh
  exact hh

end MatrixMap

namespace CompressedReplay

/-- The actual checker error is bounded by the rectangular invalid-sector potential on every
positive semidefinite joint input. Workspace entanglement and subnormalization are unrestricted.
This is the mixed-state, ancilla-preserving form of FIX (29). -/
theorem actual_sub_filled_potential_le
    {k : ℕ} {X Y A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype A]
    (io : List ((Fin k × X) × Y))
    {ρ : Matrix (A × (Fin k → Database X Y)) (A × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    QuantumRuntime.potential (actualCheck io - filledCheck io) ρ ≤
      QuantumRuntime.potential (invalidStack (k := k) (X := X) (Y := Y)) ρ := by
  classical
  rw [QuantumRuntime.potential_eq, QuantumRuntime.potential_eq]
  apply ENNReal.ofReal_le_ofReal
  have hh := ((PosSemidef.one (n := A)).kronecker
    (actual_sub_filled_gram_le_invalidStack io)).trace_mul_re_nonneg hρ
  have he (M N : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ) :
      (1 : Matrix A A ℂ) ⊗ₖ (M - N) = (1 ⊗ₖ M) - (1 ⊗ₖ N) := by
    ext a b
    simp only [kroneckerMap_apply, Matrix.sub_apply, mul_sub]
  rw [he, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hh
  linarith

end CompressedReplay

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (E : EmulatedOracle P In) (population : E.S → ℕ)

/-- Coherent control preserves a portwise one-step population-growth bound. -/
theorem population_coherent_le
    (h : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    (a b : (Σ i, In i) × E.S) (hab : E.coherent.U () a b ≠ 0) :
    population a.2 ≤ population b.2 + 1 := by
  rcases a with ⟨⟨i, a⟩, d⟩
  rcases b with ⟨⟨j, b⟩, d'⟩
  by_cases hij : i = j
  · subst j
    rw [E.coherent_U_apply_self] at hab
    exact h i _ _ hab
  · exact (hab (E.coherent_U_apply_of_ne hij a b d d')).elim

/-- One coherent call increases the support population by at most one, with an arbitrary
entangled remainder register. This is an operator-support statement, with no normalization. -/
theorem population_queryStep
    (h : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    {A : QReg} {t : ℕ} (F : QReg) (ℓ : A ≃ (Σ i, In i) × F) (r : Unit)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : QuerySupportedOn (fun a : A × E.S ↦ population a.2) (Set.Iic t) ρ) :
    QuerySupportedOn (fun a : ((Σ i, In i) × F) × E.S ↦ population a.2)
      (Set.Iic (t + 1)) ((E.coherent.toRuntime.queryStep () F ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, SubInstrument.branch_frame_apply,
    E.coherent.toRuntime_step_branch]
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ E.S)).imp
    (q' := fun a : (((Σ i, In i) × E.S) × F) ↦ population a.1.2)
    (S' := Set.Iic t) fun a ha ↦ by
      obtain ⟨b, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ E.S).surjective a
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at ha
  have h₂ := QuerySupportedOn.amplify_fst
    (q := fun a : (Σ i, In i) × E.S ↦ population a.2)
    (q' := fun a : (Σ i, In i) × E.S ↦ population a.2)
    (S := Set.Iic t) (S' := Set.Iic (t + 1))
    (fun σ hσ ↦ QuerySupportedOn.conj hσ fun a b hab hb ↦
      (E.population_coherent_le population h a b hab).trans (Nat.add_le_add_right hb 1)) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ E.S F)).imp fun a ha ↦ ?_
  obtain ⟨b, rfl⟩ := (QuantumRuntime.queryEquivOut _ E.S F).surjective a
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at ha

/-- A portwise one-step population bound lifts through arbitrary local instruments and
register-changing leaves of a coherently controlled program. The input may be any joint matrix. -/
theorem population_run (h : ∀ i a b, E.U i a b ≠ 0 → population a.2 ≤ population b.2 + 1)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) {t : ℕ}
    {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : QuerySupportedOn (fun a : A × E.S ↦ population a.2) (Set.Iic t) ρ)
    (p : Σ B, W B) :
    QuerySupportedOn (fun a : p.1 × E.S ↦ population a.2) (Set.Iic (t + q))
      ((E.coherent.toRuntime.run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn generalizing q t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact QuerySupportedOn.mono hρ (Set.Iic_subset_Iic.mpr (Nat.le_add_right t q))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun b ↦
      ih b (fun i ↦ hx i b) (QuerySupportedOn.amplify_snd hρ _)
  | queryBind _ i F ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i F ℓ k _).mp hx
    have hb : Function.update (fun _ : Unit ↦ q) i (q - 1) = fun _ ↦ q - 1 :=
      funext fun j ↦ by cases i; cases j; exact Function.update_self ..
    rw [hb] at hk
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    rw [SubInstrument.branch_toD_apply]
    cases i
    have hh := ih r (hk r) (E.population_queryStep population h F ℓ r hρ)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' hq] at hh

end EmulatedOracle

/-- Total populated cells across all compressed databases; response registers are excluded. -/
@[expose]
noncomputable def databasePopulation {k : ℕ} {X Y : Type} [Fintype X]
    (D : Fin k → Database X Y) : ℕ := ∑ i, (D i).size

section population

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- An ordinary port of the old oracle adds at most one populated cell across the whole family. -/
theorem databasePopulation_ordinary_le (i : Fin k)
    (a b : (X × Y) × (Fin k → Database X Y))
    (hab : (compressedVCOracle k X Y).U i a b ≠ 0) :
    databasePopulation a.2 ≤ databasePopulation b.2 + 1 := by
  rcases a with ⟨a, D⟩
  rcases b with ⟨b, D'⟩
  rw [compressedVCOracle_U, onFactor_apply, splitAt_apply, splitAt_apply] at hab
  split_ifs at hab with hs
  · have hsize := size_le_of_compressedOracle_apply_ne_zero hab
    change (D i).size ≤ (D' i).size + 1 at hsize
    have hother : ∀ j : {j // j ≠ i}, (D j).size = (D' j).size :=
      fun j ↦ congrArg Database.size (congrFun hs j)
    simp only [databasePopulation]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ i]
    simp only [hother]
    omega
  · exact (hab rfl).elim

variable {Cm Z : Type} [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
  [AddGroup Z] {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)

/-- Extraction leaves every database entry unchanged, so the old extraction-extended oracle
still adds at most one populated cell in a call. This holds for any extractor and encoding. -/
theorem databasePopulation_withExtract_le (i : Fin k ⊕ Unit)
    (a b : extIn k X Y Cm Z i × (Fin k → Database X Y))
    (hab : ((compressedVCOracle k X Y).withExtract ME code).U i a b ≠ 0) :
    databasePopulation a.2 ≤ databasePopulation b.2 + 1 := by
  cases i with
  | inl i => exact databasePopulation_ordinary_le i a b hab
  | inr i =>
    rcases a with ⟨⟨t, z⟩, D⟩
    rcases b with ⟨⟨t', z'⟩, D'⟩
    change extractUnitary ME code ((t, z), D) ((t', z'), D') ≠ 0 at hab
    rw [extractUnitary_apply] at hab
    split_ifs at hab with hs
    · rw [hs.2.2]
      exact Nat.le_succ _
    · exact (hab rfl).elim

/-- The original post-adversary state of the old coherent ordinary/extraction runtime is
supported on databases with at most the total query budget of populated cells. Local instruments,
adaptivity, entangled workspace, register-changing leaves and subnormalized inputs are allowed.
This theorem concerns the adversary's output before any challenger check. -/
theorem databasePopulation_post_old {L : LocalSig.{u, v}} (I : L.Interp)
    {W : QReg → Type w} {A : QReg}
    {x : QuantumComp L (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) W A}
    {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn
      (fun a : p.1 × (Fin k → Database X Y) ↦ databasePopulation a.2) (Set.Iic q)
      ((((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.jointPost
        I x ρ p).matrix) := by
  rw [QuantumRuntime.matrix_jointPost]
  have hρ : QuerySupportedOn
      (fun a : A × (Fin k → Database X Y) ↦ databasePopulation a.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ ((compressedVCOracle k X Y).withExtract ME code).init.matrix) := by
    change QuerySupportedOn _ _
      (ρ.matrix ⊗ₖ (SubState.basis (fun _ : Fin k ↦ (Database.empty : Database X Y))).matrix)
    rw [SubState.matrix_basis]
    intro a b hab
    rw [kroneckerMap_apply] at hab
    have hs := right_ne_zero_of_mul hab
    rw [Matrix.single_apply] at hs
    split_ifs at hs with he
    · simp [← he.1, ← he.2, databasePopulation, Database.size_empty]
    · exact (hs rfl).elim
  have hh := ((compressedVCOracle k X Y).withExtract ME code).population_run databasePopulation
    (databasePopulation_withExtract_le ME code) I hx hρ p
  rw [Nat.zero_add] at hh
  exact hh

end population

namespace TpDCode

variable {k : ℕ} {Dm : Fin k → Type} [∀ i, Fintype (Dm i)]

/-- A length register and one additive response register per decommitment position. The extra
value in each coordinate keeps the register nonempty even for an empty decommitment type. -/
abbrev ConcatReg (k : ℕ) (Dm : Fin k → Type) [∀ i, Fintype (Dm i)] :=
  ZMod (k + 1) × ∀ i, ZMod (Fintype.card (Dm i) + 1)

/-- Encode one decommitment in its own additive response register. -/
@[expose]
noncomputable def concatCell (i : Fin k) (a : Dm i) : ZMod (Fintype.card (Dm i) + 1) :=
  ((Fintype.equivFin (Dm i) a).val : ℕ)

/-- Each component encoding is injective. -/
theorem concatCell_injective (i : Fin k) : Function.Injective (concatCell (Dm := Dm) i) := by
  intro a b h
  apply (Fintype.equivFin (Dm i)).injective
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [concatCell, ZMod.val_natCast_of_lt
    (Nat.lt_succ_of_lt (Fintype.equivFin (Dm i) a).isLt),
    ZMod.val_natCast_of_lt (Nat.lt_succ_of_lt (Fintype.equivFin (Dm i) b).isLt)] using hv

/-- Concatenate the encoded components, padding the unused positions with zero. -/
@[expose]
noncomputable def concatPayload (j : TupleLen k) (t : TpDLen k Dm j)
    (i : Fin k) : ZMod (Fintype.card (Dm i) + 1) :=
  if h : i.val < j.len then concatCell i (t ⟨i.val, h⟩) else 0

/-- Reading a used coordinate of a concatenated payload recovers its component encoding. -/
@[simp]
theorem concatPayload_castLE (j : TupleLen k) (t : TpDLen k Dm j) (i : Fin j.len) :
    concatPayload j t (Fin.castLE j.len_le i) =
      concatCell (Fin.castLE j.len_le i) (t i) := by
  simp [concatPayload, i.isLt]

/-- A concrete injective encoding that keeps the response coordinates separate. This is the
concatenated output convention used in the disjoint-database argument of FIX (26b). -/
@[expose]
noncomputable def concat : TpDCode k Dm (ConcatReg k Dm) where
  enc t := ((t.1.len : ZMod (k + 1)), concatPayload t.1 t.2)
  enc_injective := by
    rintro ⟨j, a⟩ ⟨j', b⟩ h
    have hj : j = j' := by
      apply Subtype.ext
      apply Fin.ext
      have hv := congrArg (fun z : ConcatReg k Dm ↦ z.1.val) h
      change (j.len : ZMod (k + 1)).val = (j'.len : ZMod (k + 1)).val at hv
      rw [ZMod.val_natCast_of_lt (show j.len < k + 1 from j.1.isLt),
        ZMod.val_natCast_of_lt (show j'.len < k + 1 from j'.1.isLt)] at hv
      exact hv
    subst j'
    congr 1
    funext i
    apply concatCell_injective (Fin.castLE j.len_le i)
    have hi := congrArg (fun z : ConcatReg k Dm ↦ z.2 (Fin.castLE j.len_le i)) h
    simpa only [concatPayload_castLE] using hi

/-- At full length the payload is precisely the family of component encodings. -/
@[simp]
theorem concat_full (hk : 1 ≤ k) (t : TpDLen k Dm (TupleLen.full hk)) :
    (concat (Dm := Dm)).enc ⟨TupleLen.full hk, t⟩ =
      ((k : ZMod (k + 1)), fun i : Fin k ↦ concatCell (Dm := Dm) i (t i)) := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    exact concatPayload_castLE (TupleLen.full hk) t i

variable {Cm S : Type}

/-- Add a tuple-dependent response while leaving the tuple and database unchanged. -/
@[expose]
noncomputable def responsePerm (f : TpIC k Cm → S → ConcatReg k Dm) :
    Equiv.Perm ((TpIC k Cm × ConcatReg k Dm) × S) where
  toFun a := ((a.1.1, a.1.2 + f a.1.1 a.2), a.2)
  invFun a := ((a.1.1, a.1.2 - f a.1.1 a.2), a.2)
  left_inv a := by simp
  right_inv a := by simp

/-- Composing response translations adds their offsets; all database registers are unchanged. -/
theorem responsePerm_add (f g : TpIC k Cm → S → ConcatReg k Dm) :
    responsePerm (fun t s ↦ f t s + g t s) = responsePerm f * responsePerm g := by
  apply Equiv.ext
  rintro ⟨⟨t, z⟩, s⟩
  change ((t, z + (f t s + g t s)), s) = ((t, (z + g t s) + f t s), s)
  congr 2
  abel

/-- Response translations commute, even when their offsets depend on the database. -/
theorem responsePerm_commute (f g : TpIC k Cm → S → ConcatReg k Dm) :
    Commute (responsePerm f) (responsePerm g) := by
  change responsePerm f * responsePerm g = responsePerm g * responsePerm f
  rw [← responsePerm_add, ← responsePerm_add]
  congr 1
  funext t s
  exact add_comm _ _

/-- The length part of a concatenated extraction response is independent of the database. -/
@[expose]
noncomputable def lengthResponse (t : TpIC k Cm) (_s : S) : ConcatReg k Dm :=
  ((t.1.len : ZMod (k + 1)), 0)

/-- The response on a selected set of positions; the length register is unchanged. -/
@[expose]
noncomputable def partResponse (ME : MultiExtractor k Cm Dm S) (B : Finset (Fin k))
    (t : TpIC k Cm) (s : S) : ConcatReg k Dm :=
  (0, fun i ↦ if i ∈ B then concatPayload t.1 (ME.extract t s) i else 0)

/-- Partitioning the response coordinates splits its payload additively. -/
theorem partResponse_union (ME : MultiExtractor k Cm Dm S) (B C : Finset (Fin k))
    (hBC : Disjoint B C) (t : TpIC k Cm) (s : S) :
    partResponse ME (B ∪ C) t s = partResponse ME B t s + partResponse ME C t s := by
  apply Prod.ext (by simp [partResponse])
  funext i
  have hi := Finset.disjoint_left.mp hBC
  by_cases hb : i ∈ B <;> by_cases hc : i ∈ C
  · exact (hi hb hc).elim
  all_goals simp [partResponse, hb, hc]

/-- The full concatenated encoding is its length and all payload coordinates. -/
theorem concat_response (ME : MultiExtractor k Cm Dm S) (t : TpIC k Cm) (s : S) :
    (concat (Dm := Dm)).enc ⟨t.1, ME.extract t s⟩ =
      lengthResponse t s + partResponse ME Finset.univ t s := by
  simp [concat, lengthResponse, partResponse]

/-- Factor extraction into length, before, after, and unchecked response translations.
The identity includes every tuple length and rejected duplicate-index tuples. No locality
property of the extractor is needed for this algebraic identity. -/
theorem extractPerm_concat_factor (ME : MultiExtractor k Cm Dm S)
    (B A C : Finset (Fin k)) (hBA : Disjoint B A) (hBC : Disjoint (B ∪ A) C)
    (hcover : B ∪ A ∪ C = Finset.univ) :
    extractPerm ME (concat (Dm := Dm)) =
      responsePerm lengthResponse * responsePerm (partResponse ME B) *
        responsePerm (partResponse ME A) * responsePerm (partResponse ME C) := by
  have heq : extractPerm ME (concat (Dm := Dm)) =
      responsePerm (fun t s ↦ lengthResponse t s +
        partResponse ME B t s + partResponse ME A t s + partResponse ME C t s) := by
    apply Equiv.ext
    rintro ⟨⟨t, z⟩, s⟩
    change ((t, z + (concat (Dm := Dm)).enc ⟨t.1, ME.extract t s⟩), s) =
      ((t, z + (lengthResponse t s + partResponse ME B t s +
        partResponse ME A t s + partResponse ME C t s)), s)
    congr 3
    rw [concat_response, ← hcover, partResponse_union ME _ _ hBC,
      partResponse_union ME _ _ hBA]
    abel
  rw [heq, responsePerm_add, responsePerm_add, responsePerm_add]

/-- The coherent extraction matrix has the same factorization as its basis permutation.
Thus the factorization holds on entangled states and superpositions of extraction tuples. -/
theorem extractUnitary_concat_factor [Fintype Cm] [DecidableEq Cm]
    [Fintype S] [DecidableEq S] (ME : MultiExtractor k Cm Dm S)
    (B A C : Finset (Fin k)) (hBA : Disjoint B A) (hBC : Disjoint (B ∪ A) C)
    (hcover : B ∪ A ∪ C = Finset.univ) :
    extractUnitary ME (concat (Dm := Dm)) =
      basisMatrix (responsePerm (lengthResponse (Dm := Dm) (Cm := Cm) (S := S))) *
        basisMatrix (responsePerm (partResponse ME B)) *
        basisMatrix (responsePerm (partResponse ME A)) *
        basisMatrix (responsePerm (partResponse ME C)) := by
  rw [extractUnitary, extractPerm_concat_factor ME B A C hBA hBC hcover]
  simp only [Equiv.Perm.coe_mul, basisMatrix_comp]

end TpDCode

namespace SaltedMerkle

section factorization

open _root_.SaltedMerkle

variable {X Y Msg Salt : Type} [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)

/-- At full length, a component response depends only on its selected database. If the index
list has duplicates, all components are constant instead, so the same locality holds. -/
theorem partResponse_full_eq (hk : 1 ≤ k) (idx : Fin k → Fin k) (cm : Fin k → Y)
    (B : Finset (Fin k)) (D D' : Fin k → Database X Y)
    (hD : ∀ i ∈ B, D (idx i) = D' (idx i)) :
    TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D =
      TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D' := by
  refine Prod.ext rfl ?_
  funext i
  by_cases hi : i ∈ B
  · simp only [TpDCode.partResponse, hi, ite_true]
    simp only [TpDCode.concatPayload, dite_eq_left
      (show i.val < (TpIC.full hk idx cm).1.len from i.isLt)]
    congr 1
    simp only [multiExtract]
    split_ifs
    · change extract enc (d i) (cm i) (D (idx i)) =
        extract enc (d i) (cm i) (D' (idx i))
      rw [hD i hi]
    · rfl
  · simp [TpDCode.partResponse, hi]

/-- A rejected duplicate-index full tuple has a database-independent response on every subset
of positions, not only a database-independent complete response. -/
theorem partResponse_full_eq_of_not_injective (hk : 1 ≤ k) (idx : Fin k → Fin k)
    (cm : Fin k → Y) (B : Finset (Fin k)) (D D' : Fin k → Database X Y)
    (hidx : ¬ Function.Injective idx) :
    TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D =
      TpDCode.partResponse (multiExtract enc d) B (TpIC.full hk idx cm) D' := by
  have h : ¬ Function.Injective (TpIC.full hk idx cm).idx := hidx
  simp only [TpDCode.partResponse, multiExtract, ite_eq_right h]

/-- Distinct tuple indices send disjoint position batches to disjoint database batches. -/
theorem disjoint_image_indices {idx : Fin k → Fin k} (hidx : Function.Injective idx)
    {B A : Finset (Fin k)} (hBA : Disjoint B A) :
    Disjoint (B.image idx) (A.image idx) := by
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hj'
  exact Finset.disjoint_left.mp hBA hb (hidx hab ▸ ha)

/-- The disjoint-batch identity in FIX (26b). Its right side applies the after-extraction
factor to the original state, so it does not assert that check projectors preserve population. -/
theorem checker_batches_factor {R : Type*} [Ring R] (Aa Ab Qa Qb Va Vb Vc : R)
    (hca : Commute Ab Vc) (hcq : Commute Qb Vc)
    (haa : Commute Ab Va) (hqa : Commute Qb Va)
    (hab : Commute Vb Aa) (hqb : Commute Vb Qa)
    (hA : Commute Ab Aa) (hQ : Commute Qb Qa) :
    Ab * (Vc * Va * Vb) * Aa - Qb * (Vc * Va * Vb) * Qa =
      Vc * Va * (Aa * Ab - Qa * Qb) * Vb := by
  have h (b a : R) (hc : Commute b Vc) (hv : Commute b Va)
      (hw : Commute Vb a) (hba : Commute b a) :
      b * (Vc * Va * Vb) * a = Vc * Va * (a * b) * Vb := by
    calc
      _ = (b * Vc) * Va * (Vb * a) := by simp only [mul_assoc]
      _ = (Vc * b) * Va * (a * Vb) := by rw [hc.eq, hw.eq]
      _ = Vc * (b * Va) * a * Vb := by simp only [mul_assoc]
      _ = Vc * (Va * b) * a * Vb := by rw [hv.eq]
      _ = Vc * Va * (b * a) * Vb := by simp only [mul_assoc]
      _ = _ := by rw [hba.eq]
  rw [h Ab Aa hca haa hab hA, h Qb Qa hcq hqa hqb hQ, mul_sub, sub_mul]

end factorization

/-- The leakage sum `T_u` of FIX (35), zero at zero and one total calls. -/
@[expose]
noncomputable def oldLeakagePolynomial (u : ℕ) : ℝ :=
  if 2 ≤ u then (u : ℝ) * (u - 1 : ℕ) * (4 * u - 5 : ℕ) / 6 else 0

/-- The capped fraction of changing labels `a_u` in FIX (35). -/
@[expose]
noncomputable def oldChangingFraction (N u : ℕ) : ℝ :=
  min 1 ((2 * u - 1 : ℕ) / (N : ℝ))

section localExtraction

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]

/-- The filled-cell commutator estimate in FIX (27) for any function of a Merkle extraction
result, including a selected component batch. The tuple may contain repeated oracle indices.
The remaining database has fewer than `s` filled cells; all other databases and all ancilla
unitaries are arbitrary. -/
theorem filledCell_extraction_commutator_le
    (enc : _root_.SaltedMerkle.Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)
    (tic : TpIC k Y) (Dfix : Fin k → Database X Y) (j : Fin k)
    (D : Database X Y) (x : X) (hx : D x = none) (s : ℕ) (hsize : D.size < s)
    {κ Z : Type*} [Fintype Z] [DecidableEq Z]
    (f : TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg
      (fun i ↦ _root_.SaltedMerkle.Td Y Salt (d i))) tic.1 → κ)
    (U : κ → Matrix Z Z ℂ) (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) :
    let β := fun y ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
      (Function.update Dfix j (Function.update D x (some y))))
    let V := labelControlled (fun a : Y × Z ↦ β a.1)
      (fun a ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U a)
    ‖V * (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) * V‖ ≤
      2 * Real.sqrt (oldChangingFraction (Fintype.card Y) s) := by
  classical
  dsimp only
  let π := onlineLabel (_root_.SaltedMerkle.multiExtract enc d) ![tic] Dfix j
  let β := fun y ↦ f ((_root_.SaltedMerkle.multiExtract enc d).extract tic
    (Function.update Dfix j (Function.update D x (some y))))
  let base := f ((_root_.SaltedMerkle.multiExtract enc d).extract tic (Function.update Dfix j D))
  have hsub : (Finset.univ.filter fun y ↦ β y ≠ base) ⊆
      (Finset.univ.filter fun y ↦ π (Function.update D x (some y)) ≠ π D) := by
    intro y hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro heq
    exact (Finset.mem_filter.mp hy).2 (congrArg (fun z ↦ f (z 0)) heq)
  have hc : (Finset.univ.filter fun y ↦ β y ≠ base).card ≤ 2 * D.size + 1 :=
    (Finset.card_le_card hsub).trans
      (_root_.SaltedMerkle.card_onlineLabel_changes_le enc d tic Dfix j D x hx)
  have hfrac : ((Finset.univ.filter fun y ↦ β y ≠ base).card : ℝ) / Fintype.card Y ≤
      oldChangingFraction (Fintype.card Y) s := by
    apply le_min
    · exact (div_le_one (by positivity)).mpr (by exact_mod_cast Finset.card_le_univ _)
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (show (Finset.univ.filter fun y ↦ β y ≠ base).card ≤ 2 * s - 1 by omega)
  exact (uniformProjector_commutator_le β base U hU).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfrac) (by norm_num))

end localExtraction

/-- FIX (35): total calls `u`, ordinary mass `w`, extraction mass `e`, and raw checks `q`.
This is a numerical expression, with no claim about the probability of an experiment. -/
@[expose]
noncomputable def oldOfflineError (N u : ℕ) (w e : ℝ) (q : ℕ) : ℝ :=
  min 1 ((Real.sqrt (3 * w * u * (u - 1 : ℕ) / N) + 2 * Real.sqrt ((q : ℝ) / N) +
    2 * Real.sqrt (e * oldLeakagePolynomial u / N) +
    2 * Real.sqrt (u * oldChangingFraction N u)) ^ 2)

/-- The Merkle P4 numerical budget uses `d + 1` hash checks per opened position. -/
@[expose]
noncomputable def oldMerkleOfflineError (N d u : ℕ) (w e : ℝ) (qs : ℕ) : ℝ :=
  oldOfflineError N u w e (qs * (d + 1))

/-- No leakage accumulates before the first call. -/
@[simp] theorem oldLeakagePolynomial_zero : oldLeakagePolynomial 0 = 0 := by
  norm_num [oldLeakagePolynomial]

/-- One call gives a zero leakage polynomial. -/
@[simp] theorem oldLeakagePolynomial_one : oldLeakagePolynomial 1 = 0 := by
  norm_num [oldLeakagePolynomial]

/-- The leakage polynomial is nonnegative, including the two exceptional small budgets. -/
theorem oldLeakagePolynomial_nonneg (u : ℕ) : 0 ≤ oldLeakagePolynomial u := by
  unfold oldLeakagePolynomial
  split_ifs <;> positivity

/-- The polynomial in FIX (28) is the exact sum of the prefix leakage coefficients. -/
theorem oldLeakagePolynomial_eq_sum (u : ℕ) :
    oldLeakagePolynomial u = ∑ j ∈ Finset.range u, (j : ℝ) * (2 * j - 1) := by
  have hs (n : ℕ) :
      (∑ j ∈ Finset.range n, (j : ℝ) * (2 * j - 1)) =
        (n : ℝ) * (n - 1) * (4 * n - 5) / 6 := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [hs]
  rcases u with _ | _ | u
  · norm_num [oldLeakagePolynomial]
  · norm_num [oldLeakagePolynomial]
  · simp only [oldLeakagePolynomial, show 2 ≤ u + 1 + 1 by omega, ite_true]
    rw [Nat.cast_sub (by omega : 1 ≤ u + 1 + 1),
      Nat.cast_sub (by omega : 5 ≤ 4 * (u + 1 + 1))]
    push_cast
    ring

/-- FIX (28), as an extended-nonnegative-real Cauchy--Schwarz estimate. The masses may be
infinite; no conversion of a mass to a real number is used. This lemma only aggregates given
prefix masses and does not identify them with the extraction masses of a runtime. -/
theorem oldLeakage_sum_sqrt_le (u : ℕ) (N : ℝ≥0∞) (mass : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range u,
        (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N * mass j) ^ (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (oldLeakagePolynomial u) / N *
        ∑ j ∈ Finset.range u, mass j) ^ (2⁻¹ : ℝ) := by
  have hn (j : ℕ) : 0 ≤ (j : ℝ) * (2 * j - 1) := by
    rcases j with _ | j
    · norm_num
    · push_cast
      exact mul_nonneg (by positivity) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hs : (∑ j ∈ Finset.range u, ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N) =
      ENNReal.ofReal (oldLeakagePolynomial u) / N := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hn j),
      ← oldLeakagePolynomial_eq_sum]
  rw [← hs]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  simpa only [rpow_inv_two_rpow_two, one_div] using
    ENNReal.inner_le_Lp_mul_Lq (Finset.range u)
      (fun j ↦ (ENNReal.ofReal ((j : ℝ) * (2 * j - 1)) / N) ^ (2⁻¹ : ℝ))
      (fun j ↦ mass j ^ (2⁻¹ : ℝ)) Real.HolderConjugate.two_two

/-- The collision coefficient from NOTE (91) is bounded by the FIX (35) coefficient from
four total calls onward. The small budgets are deliberately excluded. -/
theorem collisionCoefficient_le_fix {u : ℕ} (hu : 4 ≤ u) {N w : ℝ}
    (hN : 0 < N) (hw : 0 ≤ w) :
    ((7 * u + 5) * u / (4 * N)) * min w u ≤ 3 * w * u * (u - 1 : ℕ) / N := by
  have hu' : (4 : ℝ) ≤ u := by exact_mod_cast hu
  have hc : (7 * (u : ℝ) + 5) * u / (4 * N) ≤ 3 * u * (u - 1) / N := by
    apply (div_le_div_iff₀ (by positivity) hN).mpr
    have hp : 0 ≤ (u : ℝ) * N := by positivity
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 5 * u - 17 by linarith) hp]
  calc
    _ ≤ ((7 * u + 5) * u / (4 * N)) * w :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ ≤ (3 * u * (u - 1) / N) * w := mul_le_mul_of_nonneg_right hc hw
    _ = _ := by rw [Nat.cast_sub (by omega : 1 ≤ u)]; push_cast; ring

/-- The finite error is a number in `[0, 1]`. -/
theorem oldOfflineError_mem_Icc (N u : ℕ) (w e : ℝ) (q : ℕ) :
    oldOfflineError N u w e q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (sq_nonneg _), min_le_left _ _⟩

/-- Zero total calls and zero checks give zero error for every mass parameter. -/
@[simp] theorem oldOfflineError_zero (N : ℕ) (w e : ℝ) :
    oldOfflineError N 0 w e 0 = 0 := by
  simp [oldOfflineError]

/-- The Merkle specialization retains the probability cap. -/
theorem oldMerkleOfflineError_mem_Icc (N d u : ℕ) (w e : ℝ) (qs : ℕ) :
    oldMerkleOfflineError N d u w e qs ∈ Set.Icc (0 : ℝ) 1 :=
  oldOfflineError_mem_Icc N u w e (qs * (d + 1))

end SaltedMerkle
end Quantum
