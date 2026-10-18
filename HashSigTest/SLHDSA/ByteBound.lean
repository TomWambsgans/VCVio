/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteBound
public import HashSigTest.SLHDSA.Target
public import HashSigTest.SLHDSA.WeakKeyBound

/-!
# The single-SHAKE256 bound, checked

`HashSig.SLHDSA.Security.ByteBound` bounds the forging advantage against SLH-DSA over one SHAKE256
random oracle on byte strings. This file instantiates it at the parameters of FIPS 205.

* **At the parameters of all 12 sets (the six SHAKE sets)**, for every `opt_rand` source: the
  bound at a public seed and the bound over the uniform public seed, with only the adversary's
  budget as a hypothesis. A SHA-2 set contributes only its parameters, those of its SHAKE twin.
* **Both signing modes** at SLH-DSA-SHAKE-128s (deterministic, `opt_rand = PK.seed`) and
  SLH-DSA-SHAKE-256f (hedged, `opt_rand` uniform), over the uniform public seed, with the weak-key
  term evaluated from the closed form of `honestAdrsCount`.
* **At `n = 32`, a strong public seed**: at SLH-DSA-SHAKE-256s, at the type-`7` seed, which is the
  key of no honest address, the bound at that seed has no weak-key term.
* **At `n = 32`, a weak public seed**: at the all-zero seed of SLH-DSA-SHAKE-256s, the weak-key
  term of the bound at that seed is one, so that bound says nothing there; the averaged bound
  carries the weak seeds in its term `|A_hon| / 2^256`.
* **Non-vacuity**: at SLH-DSA-SHAKE-128s with `qh = qs = 2^64` the right-hand side of the averaged
  bound is below one (`byteRhs_128s_lt_one`).
* **Hedged signing** (`opt_rand` uniform): the hedged bounds at a public seed and over the uniform
  public seed at the parameters of all 12 sets, at SLH-DSA-SHAKE-128s with the weak-key term
  evaluated, and at the strong type-`7` seed of SLH-DSA-SHAKE-256s; the averaged hedged
  right-hand side at SLH-DSA-SHAKE-128s with `qh = qs = 2^64` is below one
  (`hedgedByteRhs_128s_lt_one`), and its honest-signer terms are below those of the bound for
  every `opt_rand` source (`hedged_signerTerms_128s_lt`).
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.ByteBoundTest

open Concrete Security WeakKeyBoundTest

/-! ## At the parameters of all 12 FIPS 205 parameter sets (the six SHAKE sets) -/

/-- The bound at a public seed, at every parameter set and every `opt_rand` source. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        weakKeyMass set.validatedParams pkSeed :=
  shakeAdvantage_pure_le_securityBound_validatedParams set pkSeed adv hadv

/-- The bound over the uniform public seed, at every parameter set and every `opt_rand` source.
-/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        honestAdrsCount set.validatedParams / 2 ^ 256 :=
  shakeAdvantage_le_securityBound_validatedParams set adv hadv

/-! ## Both signing modes, with the weak-key term evaluated -/

/-- SLH-DSA-SHAKE-128s in deterministic signing (`opt_rand = PK.seed`) over the uniform public
seed: `|Y| = 256 ^ 16` and `|A_hon| = 1591788895347057694892543 ≈ 2^80.40`. -/
example (adv : UnforgeableAdversary (shakeRomScheme vp128s
      (fun pk => pure (shakeRandomizerOfPkSeed _ pk.pkSeed)) ($ᵗ (shakeCore vp128s).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp128s adv ≤
      securityBound vp128s.params (256 ^ 16) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 16 : ℕ) +
        (1591788895347057694892543 : ℕ) / 2 ^ 256 := by
  have h := shakeAdvantage_le_securityBound_validatedParams .SLHDSA_SHAKE_128s adv hadv
  rwa [show honestAdrsCount vp128s = 1591788895347057694892543 by
    rw [honestAdrsCount_eq]; decide] at h

/-- SLH-DSA-SHAKE-256f in hedged signing (`opt_rand` uniform) over the uniform public seed:
`|Y| = 256 ^ 32` and `|A_hon| = 16195218117312364562383887 ≈ 2^83.74`. -/
example (adv : UnforgeableAdversary (shakeRomScheme vp256f
      (fun _ => $ᵗ (shakeCore vp256f).Y) ($ᵗ (shakeCore vp256f).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp256f adv ≤
      securityBound vp256f.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) +
        (16195218117312364562383887 : ℕ) / 2 ^ 256 := by
  have h := shakeAdvantage_le_securityBound_validatedParams .SLHDSA_SHAKE_256f adv hadv
  rwa [show honestAdrsCount vp256f = 16195218117312364562383887 by
    rw [honestAdrsCount_eq]; decide] at h

/-! ## At `n = 32`: a strong and a weak public seed -/

/-- **A strong seed.** At SLH-DSA-SHAKE-256s, at the type-`7` public seed, which is the key of no
honest address, the bound has no weak-key term, in either signing mode. -/
example (optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y)
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure typeSevenSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) :=
  shakeAdvantage_pure_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl
    FipsParameterSet.SLHDSA_SHAKE_256s.n_le_m not_isHonestKey_typeSevenSeed adv hadv

/-- **A weak seed.** At SLH-DSA-SHAKE-256s, the weak-key term of the bound at the all-zero public
seed is one: at a weak seed the bound at that seed is trivial. -/
example (optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y)
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure zeroSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) +
        1 := by
  have h := shakeAdvantage_pure_le_securityBound_validatedParams .SLHDSA_SHAKE_256s zeroSeed adv
    hadv
  have h1 : weakKeyMass vp256s zeroSeed = 1 :=
    (SampleableType.prEvent_uniformSample_eq_one_iff _).2 isWeakKey_zeroSeed
  rwa [h1] at h

/-! ## Non-vacuity -/

open TargetTest KeyedHash.Covering in
/-- At SLH-DSA-SHAKE-128s with `qh = qs = 2^64`, the right-hand side of the bound over the uniform
public seed is below one. -/
theorem byteRhs_128s_lt_one :
    securityBound vp128s.params (2 ^ 128) 2 1 (2 ^ 64) (2 ^ 64) +
        ((2 ^ 64 : ℝ≥0∞) + 1) / (2 ^ 128 : ℕ) +
        (honestAdrsCount vp128s : ℝ≥0∞) / 2 ^ 256 < 1 := by
  have hp : vp128s.params.h = 63 ∧ vp128s.params.a = 12 ∧ vp128s.params.k = 14 := by decide
  have hV : GeneralScheme.verifyInternalQueryBound vp128s.params = 3929 := by decide
  have hA : honestAdrsCount vp128s = 1591788895347057694892543 := by
    rw [honestAdrsCount_eq]; decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, hV, hA]
  have hN : (∑ r ∈ Finset.range 15, ((r + 1) * 2 ^ r * r ^ 14 : ℕ)) < 2 ^ 72 := by decide
  have hw : ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) ≤ 1 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, ← pow_add]
    exact (ENNReal.div_self (by simp) (by simp)).le
  have hI : weightedTargetCoverBound 63 12 14 (2 ^ 64) (2 ^ 64)
      (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) ≤
        ((2 ^ 72 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
    refine (weightedTargetCoverBound_le _ _ _ _ _ _ Nat.one_le_two_pow hw).trans ?_
    simp_rw [term_128s, ← Finset.sum_mul, ← Nat.cast_sum]
    gcongr
  have key : ((2 ^ 64 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 72 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹) +
      ((2 : ℕ) * ((2 ^ 64 : ℕ) : ℝ≥0∞) + (((1 + 1) * 3929 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
      ((2 ^ 64 : ℝ≥0∞) + 1) / (2 ^ 128 : ℕ) +
      ((1591788895347057694892543 : ℕ) : ℝ≥0∞) / 2 ^ 256 < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr

/-! ## Hedged signing -/

/-- The hedged bound at a public seed, at every parameter set. -/
example (set : FipsParameterSet) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ => $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        1 / (256 ^ set.validatedParams.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ set.validatedParams.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        weakKeyMass set.validatedParams pkSeed :=
  shakeAdvantage_pure_le_securityBound_hedged_validatedParams set pkSeed adv hadv

/-- The hedged bound over the uniform public seed, at every parameter set. -/
example (set : FipsParameterSet)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ => $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        1 / (256 ^ set.validatedParams.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ set.validatedParams.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        honestAdrsCount set.validatedParams / 2 ^ 256 :=
  shakeAdvantage_le_securityBound_hedged_validatedParams set adv hadv

/-- SLH-DSA-SHAKE-128s in hedged signing over the uniform public seed, with the weak-key term
evaluated: `|Y| = 256 ^ 16`. -/
example (adv : UnforgeableAdversary (shakeRomScheme vp128s
      (fun _ => $ᵗ (shakeCore vp128s).Y) ($ᵗ (shakeCore vp128s).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp128s adv ≤
      securityBound vp128s.params (256 ^ 16) 2 1 qh qs + 1 / (256 ^ 16 : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ 16 : ℕ) : ℝ≥0∞) ^ 2 +
        (1591788895347057694892543 : ℕ) / 2 ^ 256 := by
  have h := shakeAdvantage_le_securityBound_hedged_validatedParams .SLHDSA_SHAKE_128s adv hadv
  rwa [show honestAdrsCount vp128s = 1591788895347057694892543 by
    rw [honestAdrsCount_eq]; decide] at h

/-- **A strong seed in hedged signing.** At SLH-DSA-SHAKE-256s, at the type-`7` public seed, the
hedged bound has no weak-key term. -/
example (adv : UnforgeableAdversary (shakeRomScheme vp256s
      (fun _ => $ᵗ (shakeCore vp256s).Y) (pure typeSevenSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 qh qs + 1 / (256 ^ 32 : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ 32 : ℕ) : ℝ≥0∞) ^ 2 :=
  shakeAdvantage_pure_le_securityBound_hedged_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl
    FipsParameterSet.SLHDSA_SHAKE_256s.n_le_m not_isHonestKey_typeSevenSeed adv hadv

/-- At `qh = qs = 2^64` and `|Y| = 2^128`, the honest-signer terms of the hedged bound,
`1 / |Y| + qs (qh + qs + 1) / |Y|^2`, are below the `(qs + 1) / |Y|` of the bound for every
`opt_rand` source. -/
theorem hedged_signerTerms_128s_lt :
    1 / (2 ^ 128 : ℕ) + (2 ^ 64 : ℝ≥0∞) * ((2 ^ 64 : ℝ≥0∞) + 2 ^ 64 + 1) /
        ((2 ^ 128 : ℕ) : ℝ≥0∞) ^ 2 <
      ((2 ^ 64 : ℝ≥0∞) + 1) / (2 ^ 128 : ℕ) := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_add,
    ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow,
    Nat.cast_ofNat, ne_eq, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, false_and,
    not_false_eq_true, ENNReal.add_eq_top, ENNReal.one_ne_top, or_self]
  norm_num

open TargetTest KeyedHash.Covering in
/-- At SLH-DSA-SHAKE-128s with `qh = qs = 2^64`, the right-hand side of the hedged bound over the
uniform public seed is below one. -/
theorem hedgedByteRhs_128s_lt_one :
    securityBound vp128s.params (2 ^ 128) 2 1 (2 ^ 64) (2 ^ 64) + 1 / (2 ^ 128 : ℕ) +
        (2 ^ 64 : ℝ≥0∞) * ((2 ^ 64 : ℝ≥0∞) + 2 ^ 64 + 1) / ((2 ^ 128 : ℕ) : ℝ≥0∞) ^ 2 +
        (honestAdrsCount vp128s : ℝ≥0∞) / 2 ^ 256 < 1 := by
  refine lt_of_le_of_lt ?_ byteRhs_128s_lt_one
  gcongr ?_ + _
  rw [add_assoc]
  exact add_le_add le_rfl hedged_signerTerms_128s_lt.le

end SLHDSA.ByteBoundTest
