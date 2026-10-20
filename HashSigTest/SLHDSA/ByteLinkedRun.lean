/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedRun
public import HashSig.SLHDSA.Security.ByteConformance

/-!
# The single-SHAKE256 run as a prefix of the verifying run, checked

`HashSig.SLHDSA.Security.ByteLinkedRun` bounds the advantage against SLH-DSA over one SHAKE256
oracle at `n = 32` by an event of the run against the verifying adversary. This file checks it.

* **At SLH-DSA-SHAKE-256s** the bound holds at every public seed, for any `opt_rand`, with the
  verifying adversary of an adversary making `2 ^ 64` hash and `2 ^ 64` signing queries making
  `2 ^ 64 + V` hash and `2 ^ 64` signing queries; at a public seed whose bytes are not an honest
  address key the root event never fires.
* **The clash of the final verification.** The cache holding a linked point and its `H_msg`
  reading, the two points the final non-redirected verification and the redirected one query,
  has a clash that is not the message-`PRF` key hit: `SK.prf ≠ PK.seed`, and no `H_msg` point has
  randomizer `SK.prf`. The headline classifies the clash on the linked run, before that
  verification.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteLinkedRunTest

open Concrete Security

/-- SLH-DSA-SHAKE-256s. -/
abbrev vp256s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256s

/-! ## The headline at SLH-DSA-SHAKE-256s -/

/-- **The headline with a concrete budget.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (pkSeed : (shakeCore vp256s).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeAdvantage vp256s adv ≤
        Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
            (verifyingAdv vp256s (by decide) (by decide) adv)}[
          (RedirectedWins vp256s z ∨ RunPrfKeyClash id pkSeed pkSeed z) ∨
            ¬HonestOffLinked vp256s z] ∧
      (verifyingAdv vp256s (by decide) (by decide) adv).RomQueryBound
        (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) :=
  ⟨shakeAdvantage_pure_le_verifyingAdv rfl (by decide) pkSeed adv,
    romQueryBound_verifyingAdv _ _ hadv⟩

/-- **The root event needs a weak seed.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (pkSeed : (shakeCore vp256s).PkSeed)
    (hs : ¬IsHonestKey vp256s (shakeCore vp256s)
      (adrsKeyOfList vp256s (Vector.toList (pkSeed : Bytes 32))))
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    {z : RomOutcome vp256s (shakeCore vp256s) × (hashSpec (shakeCore vp256s)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
      (verifyingAdv vp256s (by decide) (by decide) adv))) :
    HonestOffLinked vp256s z := by
  have hseed : z.1.pk.pkSeed = pkSeed := by
    simpa using pkSeed_mem_support_of_mem_support_romSchemeRun _ optRand _ hz
  exact honestOffLinked_of_mem_support_romSchemeRun hz (hseed ▸ hs)

/-! ## The clash of the final verification -/

/-- The bytes `0, 1, …, 31`. -/
def seedBytes : Bytes 32 :=
  ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31], rfl⟩

/-- A public key: seed `0, 1, …, 31`, root `7, …, 7`. -/
def pk : PublicKeyCore (shakeCore vp256s) := ⟨seedBytes, Vector.replicate 32 7⟩

/-- A message-`PRF` key: `5, …, 5`. -/
def skPrf : (shakeCore vp256s).SkPrf := Vector.replicate 32 5

/-- A node: `9, …, 9`. -/
def node : (shakeCore vp256s).Y := Vector.replicate 32 9

/-- The linked point `T(PK.seed, PK.seed, [PK.root, node])`, which the non-redirected verification
queries. -/
abbrev linkedPoint : (hashSpec (shakeCore vp256s)).Domain :=
  .inl (.thash pk.pkSeed (seedBytes : (shakeCore vp256s).AdrsKey) [pk.pkRoot, node])

/-- Its `H_msg` reading, which the redirected verification queries. -/
abbrev linkedPointHmsg : (hashSpec (shakeCore vp256s)).Domain :=
  .inl (linkedHmsg vp256s pk.pkSeed pk.pkRoot [node])

/-- The cache holding the two. -/
noncomputable def cache : (hashSpec (shakeCore vp256s)).QueryCache :=
  ((∅ : (hashSpec (shakeCore vp256s)).QueryCache).cacheQuery linkedPoint node).cacheQuery
    linkedPointHmsg (Vector.replicate _ 0)

/-- The linked point is linked. -/
example : LinkedCached vp256s pk cache :=
  ⟨.thash pk.pkSeed (seedBytes : (shakeCore vp256s).AdrsKey) [pk.pkRoot, node],
    ⟨rfl, rfl, rfl⟩, (QueryCache.isSome_cacheQuery_apply_iff _ _).2
    (Or.inr ((QueryCache.isSome_cacheQuery_apply_iff _ _).2 (Or.inl rfl)))⟩

/-- **The cache has a clash.** -/
example : (shakeEncoding vp256s (by decide) (by decide) pk.pkSeed).Clash cache := by
  refine ⟨linkedPoint, linkedPointHmsg, by simp, ?_, ?_, ?_⟩
  · exact (QueryCache.isSome_cacheQuery_apply_iff _ _).2
      (Or.inr ((QueryCache.isSome_cacheQuery_apply_iff _ _).2 (Or.inl rfl)))
  · exact (QueryCache.isSome_cacheQuery_apply_iff _ _).2 (Or.inl rfl)
  · exact (encode_linkedHmsg (vp := vp256s) [node] rfl).symm

/-- The message-`PRF` key is not the public seed. -/
example : skPrf ≠ pk.pkSeed := fun h =>
  absurd (congrArg (fun v : Bytes 32 => v.toList.head?) h) (by decide)

/-- No `H_msg` point of the cache has randomizer `SK.prf`. -/
example : ¬HmsgAtPrfKey id skPrf cache := by
  rintro ⟨ps, pr, msg, h⟩
  rcases (QueryCache.isSome_cacheQuery_apply_iff _ _).1 h with h | h
  · injection h with h
    injection h with h
    exact absurd (congrArg (fun v : Bytes 32 => v.toList.head?) h) (by decide)
  rcases (QueryCache.isSome_cacheQuery_apply_iff _ _).1 h with h | h
  · injection h with h
    cases h
  · simp at h

end SLHDSA.ByteLinkedRunTest
