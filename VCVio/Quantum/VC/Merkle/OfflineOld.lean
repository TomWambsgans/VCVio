/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerComparison
public import VCVio.Quantum.Comp.Potential
public import VCVio.CryptoFoundations.MerkleTree.Salted.Conditions

/-!
# Concatenated extraction responses and the old-oracle error

`oldOfflineError` is the real-valued function `F` of the repair note FIX (35), with
`oldMerkleOfflineError` converting opened positions to `qs * (d + 1)` raw checks.
The leakage polynomial and invalid-sector term are those of FIX (26b).
Natural subtractions are truncated before casting, and division by six is real division.
Physical parameters have `N > 0` and nonnegative ordinary and extraction masses.

`TpDCode.concat` encodes each decommitment in a separate additive coordinate, with a separate
length coordinate. Its coherent extraction matrix factors into commuting translations for any
partition of the response positions. For full Merkle tuples each part depends only on its
selected databases; duplicate-index tuples have database-independent parts. The generic
`checker_batches_factor` records the algebraic rearrangement of FIX (26b).

The leakage polynomial is the exact prefix sum in FIX (28). Its Cauchy--Schwarz estimate is
stated in `ℝ≥0∞`, including infinite masses. This module does not assert `OfflineExtractable`:
the reachable invalid-norm estimate and its transfer to the actual challenger remain necessary.
No assertion that arbitrary classical checks preserve population is used. The coefficients
four and eight in FIX (36) belong to the downstream reduction, not to this P4 error function.
-/

public section

open scoped ENNReal

namespace Quantum
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
