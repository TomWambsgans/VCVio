/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteClash
public import HashSig.SLHDSA.Security.ByteConformance
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSig.SLHDSA.Security.WeakKeyBound

/-!
# SLH-DSA over a single SHAKE256 random oracle: the unforgeability bound

FIPS 205 instantiates every hash function of the SHAKE parameter sets with SHAKE256 at a per-role
byte layout (§11.1). `HashSig.SLHDSA.Security.ByteModel` states that model, SLH-DSA over one random
oracle on byte strings (`shakeRomScheme`, `shakeAdvantage`), and
`HashSig.SLHDSA.Security.ByteConformance` shows that answering its oracle by SHAKE256 gives
FIPS 205's SHAKE internal key generation, signing and verification
(`shakeRomScheme_map_shakeAnswer`). This module bounds the forging advantage in that model.

## The bound

For `16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths
(`CanonicalAddressBounds`), at every public seed `PK.seed`, an adversary making at most `qh`
queries of the single oracle and `qs` signing queries forges with probability at most

`securityBound p |Y| 2 1 qh qs + (qs + 1) / |Y| + weakKeyMass vp PK.seed`,

with `|Y| = 256 ^ n` (`shakeAdvantage_pure_le_securityBound`). The first term is the bound of the
three-oracle model (`securityTarget_two_one`). The second, charged jointly with the events of the
first in one potential, is for an honest `PRF_msg` string `SK.prf ‖ opt_rand ‖ M` that is also
the string of another query: `qs / |Y|` for the signer's `H_msg` strings that begin with `SK.prf`,
and `1 / |Y|` for `SK.prf = PK.seed`; the forger's and the verifier's `H_msg` strings that begin
with `SK.prf` are charged inside the first term. The third is the probability, over the uniform
public root, that the public key is weak (`IsWeakKey`): that the first `32` bytes of
`PK.seed ‖ PK.root` are the key of an honest address, so that an `H_msg` string can also be a
tweakable-hash string. Averaged over the uniform public seed of FIPS 205 the third term is at
most `|A_hon| / 2^256`, with `|A_hon| = honestAdrsCount vp` (`shakeAdvantage_le_securityBound`). At
`n = 32` the weak-key event is a property of the public seed: at a seed that is not an honest
address key it never occurs, and the per-seed bound has no third term
(`shakeAdvantage_pure_le_securityBound_of_n_eq_32`); at every `n`, a seed of weak-key mass zero
has the bound without the third term
(`shakeAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`).

The `opt_rand` source is arbitrary, so these statements hold in hedged signing (`opt_rand`
uniform) and in deterministic signing (`opt_rand = PK.seed`) alike, with the same terms.

## Hedged signing

A signer's `PRF_msg` string `SK.prf ‖ opt_rand ‖ M` is an `H_msg` string
`R ‖ PK.seed ‖ PK.root ‖ M'` only when its `opt_rand` is `PK.seed`. With `opt_rand` drawn
uniformly at each signature, as in FIPS 205's hedged signing, the second term becomes

`1 / |Y| + qs (qh + qs + 1) / |Y|^2`

(`shakeAdvantage_pure_le_securityBound_hedged`, averaged `shakeAdvantage_le_securityBound_hedged`):
a clash through a signer's `PRF_msg` string needs both some `opt_rand` equal to `PK.seed`, of
probability at most `qs / |Y|`, and, independently, `SK.prf` equal to the randomizer of one of the
at most `qh + qs + 1` `H_msg` points (`prEvent_romSchemeRun_wins_or_runPrfKeyClash_le`). For any
`opt_rand` source that equals the public seed with probability at most `ε`, the second term is
`1 / |Y| + qs ε (qh + qs + 1) / |Y|`
(`shakeAdvantage_pure_le_securityBound_of_prEvent_optRand_le`).

## The argument

The routed adversary reads each byte string as a typed query of the three oracles and makes at
most as many typed queries (`routeAdv`, `romQueryBound_routeAdv`). The advantage is at most the
probability that its run against the three-oracle scheme wins, hits the message-`PRF` key
(`RunPrfKeyHit`) or has a weak public key
(`shakeAdvantage_pure_le_wins_or_runPrfKeyHit_or_isWeakKey`). The first two are bounded jointly
(`prEvent_romSchemeRun_wins_or_runPrfKeyHit_le`); in hedged signing the hit carries the
`opt_rand = PK.seed` of the clashing `PRF_msg` string (`RunPrfKeyClash`,
`shakeAdvantage_pure_le_wins_or_runPrfKeyClash_or_isWeakKey`) and is bounded with the product
term instead (`prEvent_romSchemeRun_wins_or_runPrfKeyClash_le`). The weak key is bounded by the
uniformity of the public root
(`prEvent_romSchemeRun_isWeakKey_le`), and the average over the seed by
`lintegral_add_weakKeyMass_le`. Every side condition of the three-oracle bound holds for the SHAKE
carriers: the byte laws, the key discipline under the FIPS 205 address widths, and
`|Y| = |SK.prf|`.

## Main statements

* `shakeAdvantage_pure_le_securityBound`: the bound at a public seed.
* `shakeAdvantage_le_securityBound`: the bound over the uniform public seed.
* `shakeAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`: the bound at a public seed of
  weak-key mass zero, without the weak-key term.
* `shakeAdvantage_pure_le_securityBound_of_n_eq_32`: at `n = 32`, the bound at a public seed that
  is not an honest address key, without the weak-key term.
* `shakeAdvantage_pure_le_securityBound_validatedParams`,
  `shakeAdvantage_le_securityBound_validatedParams`: both bounds at the six SHAKE parameter sets,
  with every side condition discharged. They are stated over all twelve FIPS 205 parameter sets,
  a SHA-2 set contributing only its parameters, which are those of its SHAKE twin.
* `shakeAdvantage_pure_le_securityBound_hedged`, `shakeAdvantage_le_securityBound_hedged`,
  `shakeAdvantage_pure_le_securityBound_hedged_of_weakKeyMass_eq_zero`,
  `shakeAdvantage_pure_le_securityBound_hedged_of_n_eq_32`,
  `shakeAdvantage_pure_le_securityBound_hedged_validatedParams`,
  `shakeAdvantage_le_securityBound_hedged_validatedParams`: the same forms in hedged signing, with
  `1 / |Y| + qs (qh + qs + 1) / |Y|^2` in place of `(qs + 1) / |Y|`.

## Scope

The model is that of `HashSig.SLHDSA.Security.ByteModel`: FIPS 205's internal functions, and a
SHAKE256 random oracle with `m`-byte outputs. The SHA-2 parameter sets, whose hash functions are
built from SHA-256 and SHA-512 with a compressed address, `MGF1` and `HMAC`, are not covered.

## References

* NIST FIPS 205, §9 (Algorithms 18–20), §10.2 (hedged and deterministic signing), §11.1.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

variable {vp : ValidatedParams}
  {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- **SLH-DSA over one SHAKE256 oracle, at a public seed.** For `16 ≤ n ≤ 32`, `n ≤ m` and
address fields within their FIPS 205 widths, an adversary against `shakeRomScheme` at the public
seed `pkSeed` making at most `qh` queries of the single oracle and `qs` signing queries forges with
probability at most `securityBound vp.params (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n` plus the
weak-key mass of `pkSeed`. `optRand` is arbitrary: the bound holds in hedged and deterministic
signing. -/
theorem shakeAdvantage_pure_le_securityBound (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ) + weakKeyMass vp pkSeed := by
  rw [← natCard_shakePrimitives_y]
  exact (shakeAdvantage_pure_le_wins_or_runPrfKeyHit_or_isWeakKey hn hnm hn16 pkSeed adv).trans <|
    (prEvent_or_le _ _ _).trans <| add_le_add
      (prEvent_romSchemeRun_wins_or_runPrfKeyHit_le (shakePrimitives_byteLaws vp.params)
        (keyDiscipline_shakePrimitives vp hb) le_rfl _ optRand pkSeed Function.injective_id
        pkSeed (romQueryBound_routeAdv hn hnm hadv))
      (prEvent_romSchemeRun_isWeakKey_le hb _ optRand pkSeed _)

/-- **SLH-DSA over one SHAKE256 oracle.** For `16 ≤ n ≤ 32`, `n ≤ m` and address fields within
their FIPS 205 widths, an adversary against `shakeRomScheme` with the public seed drawn uniformly,
as FIPS 205 prescribes, making at most `qh` queries of the single oracle and `qs` signing queries
forges with probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n + |A_hon| / 2^256`, with
`|A_hon| = honestAdrsCount vp` bounding the honest addresses. `optRand` is arbitrary: the bound
holds in hedged and deterministic signing. -/
theorem shakeAdvantage_le_securityBound (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ) + honestAdrsCount vp / 2 ^ 256 := by
  let _ : MeasurableSpace (shakeCore vp).PkSeed := ⊤
  have _ : DiscreteMeasurableSpace (shakeCore vp).PkSeed := ⟨fun _ => trivial⟩
  exact (shakeAdvantage_le_lintegral _ _ (fun pkSeed _ hadv' =>
    shakeAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed _ hadv') adv hadv).trans
      (lintegral_add_weakKeyMass_le hn16 _)

/-- **SLH-DSA over one SHAKE256 oracle, at a seed of weak-key mass zero.** For `16 ≤ n ≤ 32`,
`n ≤ m` and address fields within their FIPS 205 widths, an adversary against `shakeRomScheme` at a
public seed `pkSeed` of weak-key mass zero, making at most `qh` queries of the single oracle and
`qs` signing queries, forges with probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n`. `optRand` is arbitrary: the
bound holds in hedged and deterministic signing. -/
theorem shakeAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : weakKeyMass vp pkSeed = 0)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ) := by
  simpa [hs] using shakeAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at a strong public seed.** At `n = 32`,
`n ≤ m` and address fields within their FIPS 205 widths, an adversary against `shakeRomScheme` at
a public seed `pkSeed` that is not the key of an honest address, making at most `qh` queries of the
single oracle and `qs` signing queries, forges with probability at most
`securityBound vp.params (256 ^ 32) 2 1 qh qs + (qs + 1) / 256 ^ 32`. `optRand` is arbitrary: the
bound holds in hedged and deterministic signing. -/
theorem shakeAdvantage_pure_le_securityBound_of_n_eq_32 (hb : CanonicalAddressBounds vp.params)
    (hn : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _))))
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) := by
  rw [← hn]
  exact shakeAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero hb (by omega) hn.le hnm
    ((weakKeyMass_eq_zero_iff_of_n_eq_32 hn pkSeed).2 hs) adv hadv

/-! ## At the FIPS 205 parameter sets -/

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets, at a public seed.** At the
parameters of every FIPS 205 parameter set, an adversary against `shakeRomScheme` at the public
seed `pkSeed` making at most `qh` queries of the single oracle and `qs` signing queries forges with
probability at most `securityBound p (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n` plus the weak-key
mass of `pkSeed`, in hedged and deterministic signing. The statement depends on `set` only
through its parameters, which each SHA-2 set shares with its SHAKE twin: the SHAKE parameter sets
are what it covers. -/
theorem shakeAdvantage_pure_le_securityBound_validatedParams (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        weakKeyMass set.validatedParams pkSeed :=
  shakeAdvantage_pure_le_securityBound (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    set.sixteen_le_n set.n_le_32 set.n_le_m pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets.** At the parameters of
every FIPS 205 parameter set, an adversary against `shakeRomScheme` with the public seed drawn
uniformly, making at most `qh` queries of the single oracle and `qs` signing queries, forges with
probability at most
`securityBound p (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n + |A_hon| / 2^256`, with
`|A_hon| = honestAdrsCount`, in hedged and deterministic signing. The statement depends on `set`
only through its parameters, which each SHA-2 set shares with its SHAKE twin: the SHAKE parameter
sets are what it covers. -/
theorem shakeAdvantage_le_securityBound_validatedParams (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        honestAdrsCount set.validatedParams / 2 ^ 256 :=
  shakeAdvantage_le_securityBound (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    set.sixteen_le_n set.n_le_32 set.n_le_m adv hadv

/-! ## Hedged signing -/

/-- **SLH-DSA over one SHAKE256 oracle, at a public seed, when `opt_rand` rarely equals it.** For
`16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths, if `optRand pk` equals
the public seed `pkSeed` with probability at most `ε` at every public key, an adversary against
`shakeRomScheme` at `pkSeed` making at most `qh` queries of the single oracle and `qs` signing
queries forges with probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * ε * (qh + qs + 1) / 256 ^ n`
plus the weak-key mass of `pkSeed`. -/
theorem shakeAdvantage_pure_le_securityBound_of_prEvent_optRand_le
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
        qs * ε * (((qh : ℝ≥0∞) + qs + 1) / (256 ^ vp.params.n : ℕ)) + weakKeyMass vp pkSeed := by
  rw [← natCard_shakePrimitives_y]
  exact (shakeAdvantage_pure_le_wins_or_runPrfKeyClash_or_isWeakKey hn hnm hn16 pkSeed
    adv).trans <| (prEvent_or_le _ _ _).trans <| add_le_add
      (prEvent_romSchemeRun_wins_or_runPrfKeyClash_le (shakePrimitives_byteLaws vp.params)
        (keyDiscipline_shakePrimitives vp hb) le_rfl _ optRand pkSeed Function.injective_id
        pkSeed hε (romQueryBound_routeAdv hn hnm hadv))
      (prEvent_romSchemeRun_isWeakKey_le hb _ optRand pkSeed _)

/-- **SLH-DSA over one SHAKE256 oracle with hedged signing, at a public seed.** For
`16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths, with `opt_rand` drawn
uniformly at each signature, an adversary against `shakeRomScheme` at the public seed `pkSeed`
making at most `qh` queries of the single oracle and `qs` signing queries forges with probability
at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * (qh + qs + 1) / 256 ^ (2 n)`
plus the weak-key mass of `pkSeed`. -/
theorem shakeAdvantage_pure_le_securityBound_hedged (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        weakKeyMass vp pkSeed := by
  refine (shakeAdvantage_pure_le_securityBound_of_prEvent_optRand_le hb hn16 hn hnm pkSeed
    (ε := (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
    (fun _ ↦ (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le) adv hadv).trans
    (le_of_eq ?_)
  rw [natCard_shakePrimitives_y]
  simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  ring

/-- **SLH-DSA over one SHAKE256 oracle with hedged signing.** For `16 ≤ n ≤ 32`, `n ≤ m` and
address fields within their FIPS 205 widths, with `opt_rand` drawn uniformly at each signature
and the public seed drawn uniformly, as FIPS 205 prescribes, an adversary against
`shakeRomScheme` making at most `qh` queries of the single oracle and `qs` signing queries forges
with probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * (qh + qs + 1) / 256 ^ (2 n)`
`+ |A_hon| / 2^256`, with `|A_hon| = honestAdrsCount vp` bounding the honest addresses. -/
theorem shakeAdvantage_le_securityBound_hedged (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        honestAdrsCount vp / 2 ^ 256 := by
  let _ : MeasurableSpace (shakeCore vp).PkSeed := ⊤
  have _ : DiscreteMeasurableSpace (shakeCore vp).PkSeed := ⟨fun _ => trivial⟩
  exact (shakeAdvantage_le_lintegral _ _ (fun pkSeed _ hadv' =>
    shakeAdvantage_pure_le_securityBound_hedged hb hn16 hn hnm pkSeed _ hadv') adv hadv).trans
      (lintegral_add_weakKeyMass_le hn16 _)

/-- **SLH-DSA over one SHAKE256 oracle with hedged signing, at a seed of weak-key mass zero.** For
`16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths, with `opt_rand` drawn
uniformly at each signature, an adversary against `shakeRomScheme` at a public seed `pkSeed` of
weak-key mass zero, making at most `qh` queries of the single oracle and `qs` signing queries,
forges with probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * (qh + qs + 1) / 256 ^ (2 n)`. -/
theorem shakeAdvantage_pure_le_securityBound_hedged_of_weakKeyMass_eq_zero
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : weakKeyMass vp pkSeed = 0)
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) ^ 2 := by
  simpa [hs] using shakeAdvantage_pure_le_securityBound_hedged hb hn16 hn hnm pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32` with hedged signing, at a strong public seed.**
At `n = 32`, `n ≤ m` and address fields within their FIPS 205 widths, with `opt_rand` drawn
uniformly at each signature, an adversary against `shakeRomScheme` at a public seed `pkSeed` that
is not the key of an honest address, making at most `qh` queries of the single oracle and `qs`
signing queries, forges with probability at most
`securityBound vp.params (256 ^ 32) 2 1 qh qs + 1 / 256 ^ 32 + qs * (qh + qs + 1) / 256 ^ 64`. -/
theorem shakeAdvantage_pure_le_securityBound_hedged_of_n_eq_32
    (hb : CanonicalAddressBounds vp.params) (hn : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _))))
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (256 ^ 32) 2 1 qh qs + 1 / (256 ^ 32 : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ 32 : ℕ) : ℝ≥0∞) ^ 2 := by
  rw [← hn]
  exact shakeAdvantage_pure_le_securityBound_hedged_of_weakKeyMass_eq_zero hb (by omega) hn.le
    hnm ((weakKeyMass_eq_zero_iff_of_n_eq_32 hn pkSeed).2 hs) adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets with hedged signing, at a
public seed.** At the parameters of every FIPS 205 parameter set, with `opt_rand` drawn uniformly
at each signature, an adversary against `shakeRomScheme` at the public seed `pkSeed` making at
most `qh` queries of the single oracle and `qs` signing queries forges with probability at most
`securityBound p (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * (qh + qs + 1) / 256 ^ (2 n)` plus the
weak-key mass of `pkSeed`. The statement depends on `set` only through its parameters, which each
SHA-2 set shares with its SHAKE twin: the SHAKE parameter sets are what it covers. -/
theorem shakeAdvantage_pure_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        1 / (256 ^ set.validatedParams.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ set.validatedParams.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        weakKeyMass set.validatedParams pkSeed :=
  shakeAdvantage_pure_le_securityBound_hedged
    (fipsApprovedAddressBounds set).toCanonicalAddressBounds set.sixteen_le_n set.n_le_32
    set.n_le_m pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets with hedged signing.** At
the parameters of every FIPS 205 parameter set, with `opt_rand` drawn uniformly at each signature
and the public seed drawn uniformly, an adversary against `shakeRomScheme` making at most `qh`
queries of the single oracle and `qs` signing queries forges with probability at most
`securityBound p (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * (qh + qs + 1) / 256 ^ (2 n)`
`+ |A_hon| / 2^256`, with `|A_hon| = honestAdrsCount`. The statement depends on `set` only through
its parameters, which each SHA-2 set shares with its SHAKE twin: the SHAKE parameter sets are what
it covers. -/
theorem shakeAdvantage_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        1 / (256 ^ set.validatedParams.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ set.validatedParams.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        honestAdrsCount set.validatedParams / 2 ^ 256 :=
  shakeAdvantage_le_securityBound_hedged (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    set.sixteen_le_n set.n_le_32 set.n_le_m adv hadv

end SLHDSA.Security
