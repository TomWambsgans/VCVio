/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Instability
public import VCVio.Quantum.VC.Proof.Online

/-!
# Joint-label instability for salted Merkle recording

A list of `n` recorded extraction keys contributes at most `n` roots at an affected oracle.
All keys share the same half-preimage set, giving the bound `(n + 2 * D.size) / |Y|`.
The empty list has zero instability. No collision-freeness hypothesis is needed.

These are local ingredients for ePrint 2025/2166, Lemma 9.7, pp. 65–69. The sharper
joint-budget count and the time-dependent sum are from the bounds note, equations (24)–(25)
and (30), and the repair note, equation (2). This module does not assert the P5 game bound.
-/

public section

open Quantum OracleSpec
open scoped ENNReal

namespace SaltedMerkle

variable {Y : Type} [LinearOrder Y] {k : ℕ}

/-- The roots of a valid extraction tuple at one affected oracle. Repeated-index tuples have
constant extraction output, so they contribute no roots. -/
@[expose]
noncomputable def onlineRoots (tic : TpIC k Y) (j : Fin k) : Finset Y :=
  open Classical in
  if Function.Injective tic.idx then
    (Finset.univ.filter fun i ↦ (tic.2 i).1 = j).image fun i ↦ (tic.2 i).2
  else ∅

/-- Each extraction tuple contributes at most one root at an affected oracle. -/
theorem card_onlineRoots_le (tic : TpIC k Y) (j : Fin k) : (onlineRoots tic j).card ≤ 1 := by
  classical
  unfold onlineRoots
  split_ifs with hinj
  · refine Finset.card_le_one.mpr ?_
    intro y hy z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have he : a = b := hinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    rw [he]
  · simp

/-- A list of extraction keys has at most as many relevant roots as keys. -/
theorem card_biUnion_onlineRoots_le {n : ℕ} (tics : Fin n → TpIC k Y) (j : Fin k) :
    (Finset.univ.biUnion fun a ↦ onlineRoots (tics a) j).card ≤ n := by
  classical
  calc _ ≤ ∑ a : Fin n, (onlineRoots (tics a) j).card := Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin n, 1 := Finset.sum_le_sum fun a _ ↦ card_onlineRoots_le (tics a) j
    _ = n := by simp

variable {X Msg Salt : Type} [DecidableEq X] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : Encoding X Y Msg Salt) (d : Fin k → ℕ)

/-- A fresh answer outside the relevant roots and shared half-preimages preserves every
extraction in a list, including tuples with repeated indices. -/
theorem onlineLabel_list_update_eq {n : ℕ} (tics : Fin n → TpIC k Y)
    (Dfix : Fin k → Database X Y) (j : Fin k) (D : Database X Y) (x : X) (y : Y)
    (hx : D x = none) (hy : y ∉ halfPreimages enc D)
    (hroot : ∀ a, y ∉ onlineRoots (tics a) j) :
    onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) =
      onlineLabel (multiExtract enc d) tics Dfix j D := by
  classical
  funext a
  by_cases hinj : Function.Injective (tics a).idx
  · have hs (i : Fin (tics a).1.len) (hi : ((tics a).2 i).1 = j) :
        y ∉ insert ((tics a).2 i).2 (halfPreimages enc D) := by
      simp only [Set.mem_insert_iff, not_or]
      refine ⟨?_, hy⟩
      intro he
      apply hroot a
      simp only [onlineRoots, hinj, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, he.symm⟩
    have h := multiExtract_update_eq enc d (tics a) (Function.update Dfix j D) j
      (by simpa using hx) (by simpa using hs)
    simpa [onlineLabel, Function.update_idem] using h
  · simp [onlineLabel, multiExtract, hinj]

variable [Fintype X]

open scoped Classical in
/-- A list of `n` keys shares its half-preimage contribution: its changing answers number at
most `n + 2 * D.size`, rather than `n * (1 + 2 * D.size)`. -/
theorem card_onlineLabel_list_changes_le {n : ℕ} (tics : Fin n → TpIC k Y)
    (Dfix : Fin k → Database X Y) (j : Fin k) (D : Database X Y) (x : X)
    (hx : D x = none) :
    (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) tics Dfix j D).card ≤ n + 2 * D.size := by
  classical
  let roots := Finset.univ.biUnion fun a ↦ onlineRoots (tics a) j
  have hsub : (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) tics Dfix j D) ⊆
        roots ∪ (halfPreimages enc D).toFinset := by
    intro y hy
    by_contra hn
    simp only [Finset.mem_union, Set.mem_toFinset, not_or] at hn
    apply (Finset.mem_filter.mp hy).2
    apply onlineLabel_list_update_eq enc d tics Dfix j D x y hx hn.2
    intro a ha
    exact hn.1 (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ha⟩)
  have hh := ncard_halfPreimages_le_of_finite enc D
  rw [ncard_support_eq_size, Set.ncard_eq_toFinset_card'] at hh
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (card_biUnion_onlineRoots_le tics j) hh))

omit [Fintype X] in
/-- The joint-label instability for `n` extraction keys at databases of size at most `s`. -/
theorem instability_onlineLabel_list_le [Finite X] [UniformAnswerMeasure (X →ₒ Y)]
    {n : ℕ} (tics : Fin n → TpIC k Y) (Dfix : Fin k → Database X Y)
    (j : Fin k) (s : ℕ) :
    Database.instability (onlineLabel (multiExtract enc d) tics Dfix j) (s + 1) ≤
      min 1 ((n + 2 * s : ℝ≥0∞) / Fintype.card Y) := by
  classical
  let _ := Fintype.ofFinite X
  refine le_min (Database.instability_le_one _ _) ?_
  rw [Database.instability_eq_iSup]
  refine iSup_le fun l ↦ iSup_le fun D ↦ iSup_le fun hl ↦ iSup_le fun hD ↦
    iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  subst l
  have hc := card_onlineLabel_list_changes_le enc d tics Dfix j D x hx
  have hs : D.size ≤ s := by omega
  have hc' : (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) tics Dfix j D).card ≤ n + 2 * s := by omega
  gcongr
  exact_mod_cast hc'

omit [Fintype X] in
/-- The empty list has zero instability at every population bound. -/
theorem instability_onlineLabel_empty [Finite X] [AnswerMeasure (X →ₒ Y)]
    (tics : Fin 0 → TpIC k Y) (Dfix : Fin k → Database X Y) (j : Fin k) (s : ℕ) :
    Database.instability (onlineLabel (multiExtract enc d) tics Dfix j) s = 0 := by
  have he : onlineLabel (multiExtract enc d) tics Dfix j =
      fun _ : Database X Y ↦ fun a : Fin 0 ↦ Fin.elim0 a := by
    funext D a
    exact Fin.elim0 a
  rw [he, Database.instability_const]

/-- The joint-budget arithmetic in the bounds note, equation (30): a nonempty record set
and the remaining database fit into the budget before the active query. -/
theorem online_joint_count_le {n r h : ℕ} (hn : 1 ≤ n) (hcost : r + n ≤ h - 1) :
    n + 2 * r ≤ 2 * h - 3 := by
  omega

end SaltedMerkle

namespace Quantum

/-- The local weight of the query at zero-based position `j`. The first query has weight zero;
the later weights are the odd numbers in the bounds note, equation (30). -/
@[expose]
def onlineStepWeight (j : ℕ) : ℕ := 2 * j - 1

/-- The time-dependent local weights sum to the square of the number of later queries. -/
theorem sum_onlineStepWeight (t : ℕ) :
    ∑ j ∈ Finset.range t, onlineStepWeight j = (t - 1) ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    unfold onlineStepWeight
    cases t with
    | zero => norm_num
    | succ t =>
      simp only [Nat.add_sub_cancel]
      have he : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
      rw [he]
      ring

/-- Weighted Cauchy–Schwarz gives the exact constant in the bounds note, equation (30).
The masses are arbitrary nonnegative reals; relating them to a recording execution is a
separate operator argument. -/
theorem online_weighted_sum_sq_le (t : ℕ) (mass : ℕ → ℝ) (hmass : ∀ j, 0 ≤ mass j)
    (w N : ℝ) (hN : 0 < N) (hw : ∑ j ∈ Finset.range t, mass j ≤ w) :
    (24 / N) * (∑ j ∈ Finset.range t,
      Real.sqrt ((onlineStepWeight j : ℝ) * mass j)) ^ 2 ≤
      24 * w * (t - 1 : ℕ) ^ 2 / N := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range t)
    (fun j ↦ Real.sqrt (onlineStepWeight j)) (fun j ↦ Real.sqrt (mass j))
  simp only [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (hmass _)] at hc
  have he : ∑ j ∈ Finset.range t, (onlineStepWeight j : ℝ) = (t - 1 : ℕ) ^ 2 := by
    exact_mod_cast sum_onlineStepWeight t
  rw [he] at hc
  simp only [← Real.sqrt_mul (Nat.cast_nonneg _)] at hc
  calc
    _ ≤ (24 / N) * ((t - 1 : ℕ) ^ 2 * w) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = _ := by ring

/-- The capped numerical online error from the bounds note, equation (30), and the repair
note, equation (2). This defines the target scalar without asserting a security theorem. -/
@[expose]
noncomputable def merkleOnlineError (N t : ℕ) (w : ℝ≥0∞) : ℝ≥0∞ :=
  min 1 (24 * w * (t - 1 : ℕ) ^ 2 / N)

/-- The numerical error is always at most one. -/
theorem merkleOnlineError_le_one (N t : ℕ) (w : ℝ≥0∞) : merkleOnlineError N t w ≤ 1 :=
  min_le_left _ _

/-- Zero queries have zero numerical online error, including infinite mass budgets. -/
@[simp]
theorem merkleOnlineError_zero (N : ℕ) (w : ℝ≥0∞) : merkleOnlineError N 0 w = 0 := by
  simp [merkleOnlineError]

/-- A single query has zero numerical online error, including infinite mass budgets. -/
@[simp]
theorem merkleOnlineError_one (N : ℕ) (w : ℝ≥0∞) : merkleOnlineError N 1 w = 0 := by
  simp [merkleOnlineError]

end Quantum
