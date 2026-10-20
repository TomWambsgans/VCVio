/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedBound
public import HashSigTest.SLHDSA.WeakKeyBound

/-!
# The events of the verifying run, bounded with a further charge, checked

`HashSig.SLHDSA.Security.ByteLinkedBound` bounds the events of the verifying run at `n = 32`,
with a further charge. This file checks it at SLH-DSA-SHAKE-256s, for an adversary making
`2 ^ 64` hash and `2 ^ 64` signing queries.

* **No further event.** The run against the verifying adversary fires a target collision, a
  mixed hidden-value hit, the key clash or coverage with probability at most
  `securityBound (2, 1) (2 ^ 64 + V) (2 ^ 64) + (2 ^ 64 + 1) / |Y|`.
* **The hook.** With a further charge whose transport and budget hold, the advantage is at most
  that bound plus the cost `κ`, here `(2 ^ 64 + 1) / |Y|`, in the deterministic form, and the
  hedged form takes the same hook.
* **The run point.** The run point of a deferred point is the rebuilt transcript on the merged
  cache, by definition.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.ByteLinkedBoundTest

open Concrete Security WeakKeyBoundTest

/-- The key discipline at SLH-DSA-SHAKE-256s. -/
theorem keyDiscipline_vp256s : (shakeCore vp256s).KeyDiscipline vp256s :=
  keyDiscipline_shakePrimitives vp256s
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds

/-! ## No further event -/

/-- **The landed shape at SLH-DSA-SHAKE-256s, with a concrete budget.** -/
theorem prEvent_romSchemeRun_verifyingAdv_le_vp256s
    {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
        (verifyingAdv vp256s (by decide) (by decide) adv)}[
      ((RunTargetCollision (shakeCore vp256s) (Equiv.refl _) z ∨ RunHiddenHitMixed vp256s z) ∨
        RunPrfKeyClash id pkSeed pkSeed z) ∨ RunItsrCovered (shakeCore vp256s) z] ≤
    securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
        (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y :=
  prEvent_romSchemeRun_verifyingAdv_le keyDiscipline_vp256s rfl (by decide) adv hadv

/-! ## The hook -/

/-- **The deterministic bound with a further charge at SLH-DSA-SHAKE-256s.** With the cost
`(2 ^ 64 + 1) / |Y|` covering a further charge whose transport and budget hold. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) (χ : DeferredCharge (shakeCore vp256s) pkSeed)
    (hX : χ.Charges (verifyingAdv vp256s (by decide) (by decide) adv)
      fun z ↦ VirtualHit vp256s z ∨ LinkedHonestInput vp256s z)
    (hbud : χ.WithinBudget (verifyingAdv vp256s (by decide) (by decide) adv)
      (fun C ↦ hmsgCharge (shakeCore vp256s) C + (Nat.card (shakeCore vp256s).Y : ℝ≥0∞)⁻¹)
      ((2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp256s.params) +
          ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y)) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
          (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / Nat.card (shakeCore vp256s).Y :=
  shakeAdvantage_pure_le_securityBound_add
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
    hadv χ _ (div_natCard_ne_top (by simp)) hX hbud

/-- **The hedged form takes the same hook.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {pkSeed : (shakeCore vp256s).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε)
    (χ : DeferredCharge (shakeCore vp256s) pkSeed) (κ : ℝ≥0∞) (hκ : κ ≠ ⊤)
    (hX : χ.Charges (verifyingAdv vp256s (by decide) (by decide) adv)
      fun z ↦ VirtualHit vp256s z ∨ LinkedHonestInput vp256s z)
    (hbud : χ.WithinBudget (verifyingAdv vp256s (by decide) (by decide) adv)
      (fun _ ↦ (Nat.card (shakeCore vp256s).Y : ℝ≥0∞)⁻¹)
      ((2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp256s.params) +
          1) / Nat.card (shakeCore vp256s).Y + κ)) :
    shakeAdvantage vp256s adv ≤
      securityBound vp256s.params (Nat.card (shakeCore vp256s).Y) 2 1
          (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) +
        1 / Nat.card (shakeCore vp256s).Y +
        ((2 ^ 64 : ℕ) : ℝ≥0∞) * ε * (((2 ^ 64 + GeneralScheme.verifyInternalQueryBound
          vp256s.params : ℕ) : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
          Nat.card (shakeCore vp256s).Y + κ :=
  shakeAdvantage_pure_le_securityBound_add_hedged
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
    hadv hε χ κ hκ hX hbud

/-! ## The run point -/

/-- The run point of a deferred point is the rebuilt transcript on the merged cache. -/
example {pkSeed : (shakeCore vp256s).PkSeed}
    (w : (DeriveOutcome (shakeCore vp256s) × LabState (shakeCore vp256s) ×
      List (DeriveQuery (shakeCore vp256s) ⊕ NodeKey (shakeCore vp256s))) ×
      LabState (shakeCore vp256s) × ((shakeCore vp256s).SkSeed × (shakeCore vp256s).SkPrf)) :
    deferredRunPoint pkSeed w = (DeriveOutcome.fill (shakeCore vp256s) w.2.2 w.1.1,
      (secretEncoding (shakeCore vp256s) (Equiv.refl _) pkSeed).merge w.2.2
        ((slhGraph (shakeCore vp256s) pkSeed).toSplitCache w.2.1)) :=
  rfl

end SLHDSA.ByteLinkedBoundTest
