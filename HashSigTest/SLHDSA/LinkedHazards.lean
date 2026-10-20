/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LinkedHazards
public import HashSigTest.SLHDSA.Target
public import HashSigTest.SLHDSA.WeakKeyBound

/-!
# The virtual hit and the honest input at a linked point, charged, checked

`HashSig.SLHDSA.Security.LinkedHazards` bounds the advantage against SLH-DSA over one SHAKE256
oracle at `n = 32`, at every public seed, by
`securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + (qs + 1) / |Y|`. This file checks
it at SLH-DSA-SHAKE-256s and SLH-DSA-SHAKE-256f for an adversary making `2 ^ 64` hash and
`2 ^ 64` signing queries.

* **The bound at both parameter sets**, in the deterministic and the hedged form, at every
  public seed, with no condition on the seed.
* **The bound is below one.** With `V = 8444` at 256s and `V = 17522` at 256f, the right-hand
  side is below one (`rhs_256s_lt_one`, `rhs_256f_lt_one`), so the advantage is below one at
  every public seed (`shakeAdvantage_lt_one_256s`, `shakeAdvantage_lt_one_256f`); the coverage
  term is bounded crudely here, by about `2 ^ -139` at 256s and `2 ^ -65` at 256f.
* **The levels.** Per query, `-log₂ (bound / qh)` at `qh = qs = 2 ^ 64` is `253.68` at 256s and
  `253.59` at 256f; at `qh = qs = 2 ^ 40` it is `254.00` at both. In the hedged form with uniform
  `opt_rand` (`ε = 2 ^ -256`) it is `254.00` at 256s and `253.89` at 256f at `2 ^ 64`, and `254.42`
  at both at `2 ^ 40`. These are computed with the coverage term at its exact value, not the crude
  bound checked here.
* **Negative controls.** Two equal cells always form a pair hazard (`pairHazard_self`), so the
  root's pair charge needs the root to be no node's child; and at a signing budget of `2 ^ 256`
  the further charge alone is at least one (`one_le_qs_add_one_div_256`), so the bound depends on
  `qs`.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.LinkedHazardsTest

open Concrete Security WeakKeyBoundTest KeyedHash.Covering

/-! ## The bound at SLH-DSA-SHAKE-256s and SLH-DSA-SHAKE-256f -/

/-- The verifier's query bound at SLH-DSA-SHAKE-256s. -/
theorem verifyInternalQueryBound_256s :
    GeneralScheme.verifyInternalQueryBound vp256s.params = 8444 := by
  decide

/-- The verifier's query bound at SLH-DSA-SHAKE-256f. -/
theorem verifyInternalQueryBound_256f :
    GeneralScheme.verifyInternalQueryBound vp256f.params = 17522 := by
  decide

/-- **The bound at SLH-DSA-SHAKE-256s**, at every public seed. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y := by
  simpa only [verifyInternalQueryBound_256s] using
    shakeAdvantage_pure_le_securityBound_add_of_n_eq_32
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
      hadv

/-- **The bound at SLH-DSA-SHAKE-256f**, at every public seed. -/
example {optRand : PublicKeyCore (shakeCore vp256f) → ProbComp (shakeCore vp256f).Y}
    {pkSeed : (shakeCore vp256f).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256f optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeAdvantage vp256f adv ≤
      securityBound vp256f.params (Nat.card (shakeCore vp256f).Y) 2 1 (2 ^ 64 + 17522) (2 ^ 64) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256f).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256f).Y := by
  simpa only [verifyInternalQueryBound_256f] using
    shakeAdvantage_pure_le_securityBound_add_of_n_eq_32
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_256f).toCanonicalAddressBounds rfl (by decide) adv
      hadv

/-- **The hedged bound at SLH-DSA-SHAKE-256s**, at every public seed. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
        1 / Nat.card (shakeCore vp256s).Y +
        ((2 ^ 64 : ℕ) : ℝ≥0∞) * ε * (((2 ^ 64 + 8444 : ℕ) : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
          Nat.card (shakeCore vp256s).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y := by
  simpa only [verifyInternalQueryBound_256s] using
    shakeAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
      hadv hε

/-! ## The bound is below one -/

/-- With `2 ^ 64` signing queries, `h ≥ 64` and at most one weighted coverer expected, the
weighted coverage term is at most `∑ r ≤ k, (r + 1) · r ^ k` times `2 ^ (-a k)`. -/
theorem weightedTargetCoverBound_le_of_le_h {h a k qw : ℕ} {w : ℝ≥0∞} (hh : 64 ≤ h)
    (hw : (qw : ℝ≥0∞) * w ≤ 1) :
    weightedTargetCoverBound h a k (2 ^ 64) qw w ≤
      ((∑ r ∈ Finset.range (k + 1), (r + 1) * r ^ k : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by
  refine (TargetTest.weightedTargetCoverBound_le _ _ _ _ _ _ Nat.one_le_two_pow hw).trans ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  have h1 : (((2 ^ 64) ^ r : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ h)⁻¹) ^ r ≤ 1 := by
    rw [← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_mul]
    rw [← div_eq_mul_inv]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_right r hh)
  calc (((r + 1) * (2 ^ 64) ^ r * r ^ k : ℕ) : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k)
      = (((r + 1) * r ^ k : ℕ) : ℝ≥0∞) *
          ((((2 ^ 64) ^ r : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ h)⁻¹) ^ r) *
          (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by push_cast; ring
    _ ≤ (((r + 1) * r ^ k : ℕ) : ℝ≥0∞) * 1 * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by gcongr
    _ = _ := by rw [mul_one]

/-- At most one of the forger's `H_msg` values is expected to cover. -/
theorem natCast_mul_div_le_one (V : ℕ) (hV : V ≤ 2 ^ 64) :
    ((2 ^ 64 + V : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≤ 1 := by
  rw [← mul_div_assoc, ← Nat.cast_mul]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast (Nat.mul_le_mul_right _ (by omega : 2 ^ 64 + V ≤ 2 ^ 65)).trans
    (by norm_num)

/-- **The bound at SLH-DSA-SHAKE-256s is below one.** -/
theorem rhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
  have hp : vp256s.params.h = 64 ∧ vp256s.params.a = 14 ∧ vp256s.params.k = 22 := by decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, verifyInternalQueryBound_256s]
  have hN : (∑ r ∈ Finset.range 23, (r + 1) * r ^ 22 : ℕ) < 2 ^ 104 := by decide
  have hI := weightedTargetCoverBound_le_of_le_h (h := 64) (a := 14) (k := 22) le_rfl
    (natCast_mul_div_le_one 8444 (by norm_num))
  have key : ((2 ^ 64 + 8444 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 104 : ℕ) : ℝ≥0∞) *
        (((2 : ℝ≥0∞) ^ 14)⁻¹) ^ 22) +
      ((2 : ℕ) * ((2 ^ 64 + 8444 : ℕ) : ℝ≥0∞) + (((1 + 1) * 8444 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr
  exact hI.trans (by gcongr)

/-- **The bound at SLH-DSA-SHAKE-256f is below one.** -/
theorem rhs_256f_lt_one :
    securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64 + 17522) (2 ^ 64) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
  have hp : vp256f.params.h = 68 ∧ vp256f.params.a = 9 ∧ vp256f.params.k = 35 := by decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, verifyInternalQueryBound_256f]
  have hN : (∑ r ∈ Finset.range 36, (r + 1) * r ^ 35 : ℕ) < 2 ^ 186 := by decide
  have hI := weightedTargetCoverBound_le_of_le_h (h := 68) (a := 9) (k := 35) (by norm_num)
    (natCast_mul_div_le_one 17522 (by norm_num))
  have key : ((2 ^ 64 + 17522 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 186 : ℕ) : ℝ≥0∞) *
        (((2 : ℝ≥0∞) ^ 9)⁻¹) ^ 35) +
      ((2 : ℕ) * ((2 ^ 64 + 17522 : ℕ) : ℝ≥0∞) + (((1 + 1) * 17522 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr
  exact hI.trans (by gcongr)

/-- `|Y| = 2 ^ 256` at SLH-DSA-SHAKE-256s. -/
theorem natCard_y_256s : Nat.card (shakeCore vp256s).Y = 2 ^ 256 :=
  (natCard_shakePrimitives_y _).trans (by decide)

/-- `|Y| = 2 ^ 256` at SLH-DSA-SHAKE-256f. -/
theorem natCard_y_256f : Nat.card (shakeCore vp256f).Y = 2 ^ 256 :=
  (natCard_shakePrimitives_y _).trans (by decide)

/-- **The advantage at SLH-DSA-SHAKE-256s is below one** at every public seed, for `2 ^ 64` hash
and `2 ^ 64` signing queries. -/
theorem shakeAdvantage_lt_one_256s
    {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) : shakeAdvantage vp256s adv < 1 := by
  refine lt_of_le_of_lt ?_ rhs_256s_lt_one
  simpa only [verifyInternalQueryBound_256s, natCard_y_256s] using
    shakeAdvantage_pure_le_securityBound_add_of_n_eq_32
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
      hadv

/-- **The advantage at SLH-DSA-SHAKE-256f is below one** at every public seed, for `2 ^ 64` hash
and `2 ^ 64` signing queries. -/
theorem shakeAdvantage_lt_one_256f
    {optRand : PublicKeyCore (shakeCore vp256f) → ProbComp (shakeCore vp256f).Y}
    {pkSeed : (shakeCore vp256f).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256f optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) : shakeAdvantage vp256f adv < 1 := by
  refine lt_of_le_of_lt ?_ rhs_256f_lt_one
  simpa only [verifyInternalQueryBound_256f, natCard_y_256f] using
    shakeAdvantage_pure_le_securityBound_add_of_n_eq_32
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_256f).toCanonicalAddressBounds rfl (by decide) adv
      hadv

/-! ## Negative controls -/

/-- A drawn cell paired with itself is a pair hazard: the pair charge of the root needs the root
to be distinct from the child it is compared with. -/
theorem pairHazard_self {ι X K R : Type} {pub : OracleSpec ι} (c : X ⊕ K)
    {st : RelabelState pub X K R} {v : R} (hc : st.2 c = some v) :
    CanonicalGraph.PairHazard X K R c c st :=
  ⟨v, hc, hc⟩

/-- At `2 ^ 256` signing queries the further charge `(qs + 1) / 2 ^ 256` alone is at least one. -/
theorem one_le_qs_add_one_div_256 :
    1 ≤ (((2 ^ 256 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
  exact le_self_add

end SLHDSA.LinkedHazardsTest
