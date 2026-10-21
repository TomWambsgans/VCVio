/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSigTest.SLHDSA.CoverageBound
public import HashSig.SLHDSA.Security.ByteBound

/-!
# Strong unforgeability of SLH-DSA, checked

The headline bounds of `HashSig.SLHDSA.Security.CoverageBound` and
`HashSig.SLHDSA.Security.ByteBound` bound the strong forging advantage: a forgery is a valid pair
of message and signature that the signing oracle never returned. Their non-vacuity at the FIPS 205
parameter sets is checked in `HashSigTest.SLHDSA.ByteBound`, `HashSigTest.SLHDSA.LinkedHazards` and
`HashSigTest.SLHDSA.CoverageBound`. This file checks two further facts.

* **The existential forms.** Each existential headline is re-derived from its strong form through
  `unforgeableAdvantage_le_strongUnforgeableAdvantage` or `shakeAdvantage_le_shakeStrongAdvantage`,
  at the same right-hand side.
* **Negative control.** A transcript whose forged pair is a logged pair is no strong win, whatever
  its verdict; one whose message is logged with another signature is a strong win and no
  existential win.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.StrongUnforgeabilityTest

open Concrete Security

/-! ## The existential forms, re-derived -/

section Existential

variable {vp : ValidatedParams}

/-- The existential averaged target at a SHAKE bundle, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand pkSeedDist)) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp))) adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ adv).trans
    (strongUnforgeableAdvantage_romScheme_le _ (CoverageBoundTest.securityTarget_shake vp hb e
      optRand) pkSeedDist ⟨adv.main⟩ hadv)

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- The existential bound at a public seed, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBound vp qh qs + weakKeyMass vp pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed ⟨adv.main⟩ hadv)

/-- The existential averaged bound, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBound vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBound vp qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound hb hn16 hn hnm ⟨adv.main⟩ hadv)

/-- The existential averaged bound in hedged signing, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBoundHedged vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBoundHedged vp qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged hb hn16 hn hnm ⟨adv.main⟩ hadv)

variable (set : FipsParameterSet)

/-- The existential bound at a public seed at the parameter sets, from the strong one. -/
example {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      byteBound set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_validatedParams set pkSeed ⟨adv.main⟩ hadv)

/-- The existential hedged bound at a public seed at the parameter sets, from the strong one. -/
example (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      byteBoundHedged set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams set pkSeed ⟨adv.main⟩ hadv)

/-- The existential every-seed bound at the parameter sets with `n = 32`, from the strong one. -/
example (hn : set.validatedParams.params.n = 32)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ everySeedBound set.validatedParams qh qs :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_add_validatedParams set hn pkSeed ⟨adv.main⟩ hadv)

/-- The existential hedged every-seed bound at the parameter sets with `n = 32`, from the strong
one. -/
example (hn : set.validatedParams.params.n = 32) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ everySeedBoundHedged set.validatedParams qh qs :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams set hn pkSeed
      ⟨adv.main⟩ hadv)

/-- The existential averaged bound at the parameter sets, from the strong one. -/
example {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ byteBound set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBound set.validatedParams qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_validatedParams set ⟨adv.main⟩ hadv)

/-- The existential averaged hedged bound at the parameter sets, from the strong one. -/
example (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ byteBoundHedged set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBoundHedged set.validatedParams qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged_validatedParams set ⟨adv.main⟩ hadv)

end Existential

/-! ## Negative control: a replayed pair is not a strong win -/

/-- A transcript whose forged pair of message and signature is a logged pair is no strong win,
whatever its verification verdict. -/
theorem strongWins_eq_false_of_mem_log {M PK SK S : Type} (o : UnforgeableTranscript M PK SK S)
    (h : ⟨o.msg, o.sig⟩ ∈ o.log) : o.strongWins = false := by
  cases hw : o.strongWins
  · rfl
  · exact absurd h ((o.strongWins_eq_true_iff.1 hw).1)

/-- A transcript that signs message `0` as `1`. -/
def signedOnce (σ : ℕ) : UnforgeableTranscript ℕ Unit Unit ℕ :=
  ⟨(), (), [⟨0, 1⟩], 0, σ, true⟩

/-- Replaying the logged pair `(0, 1)` with an accepting verdict is not a strong win. -/
example : (signedOnce 1).strongWins = false :=
  strongWins_eq_false_of_mem_log _ (by simp [signedOnce])

/-- A second, accepted signature `2` on the logged message `0` is a strong win but no existential
win: the strong notion counts it. -/
example : (signedOnce 2).strongWins = true ∧ (signedOnce 2).wins = false := by
  refine ⟨(UnforgeableTranscript.strongWins_eq_true_iff _).2 ⟨by simp [signedOnce], rfl⟩, ?_⟩
  cases hw : (signedOnce 2).wins
  · rfl
  · exact absurd ((UnforgeableTranscript.wins_eq_true_iff _).1 hw).1 (by simp [signedOnce])

end SLHDSA.StrongUnforgeabilityTest
