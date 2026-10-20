/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedView
public import HashSigTest.SLHDSA.WeakKeyBound
import all HashSigTest.SLHDSA.ByteLinkedRun

/-!
# The bad events of the verifying run, read through the linked redirect, checked

`HashSig.SLHDSA.Security.ByteLinkedView` bounds the advantage against SLH-DSA over one SHAKE256
oracle at `n = 32` by the events of the run against the verifying adversary. This file checks it.

* **At SLH-DSA-SHAKE-256s** the bound holds at every public seed, for any `opt_rand`, with the
  verifying adversary of an adversary making `2 ^ 64` hash and `2 ^ 64` signing queries making
  `2 ^ 64 + V` hash and `2 ^ 64` signing queries.
* **Off a weak seed.** At the public seed `typeSevenSeed`, whose bytes are not an honest address
  key, no run point has a virtual hit or an honest input at a linked point, so the headline's
  events are those of the bridge on the cache and its view.
* **A cached linked point is not an honest input.** At the weak seed of
  `HashSigTest.SLHDSA.ByteLinkedRun`, the cache holding the linked point that the non-redirected
  verification queries, and its `H_msg` reading, has a cached linked point but no honest entry at
  all, so neither `VirtualHit` nor `LinkedHonestInput` holds there: the root event is not read off
  cache content.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteLinkedViewTest

open Concrete Security ByteLinkedRunTest

/-! ## The headline at SLH-DSA-SHAKE-256s -/

/-- **The headline with a concrete budget.** -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (pkSeed : (shakeCore vp256s).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeAdvantage vp256s adv ≤
        Pr{let z ← romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand (pure pkSeed)
            (verifyingAdv vp256s (by decide) (by decide) adv)}[
          ((RunTargetCollision (shakeCore vp256s) (Equiv.refl _) z ∨ RunHiddenHitMixed vp256s z) ∨
            (RunPrfKeyClash id pkSeed pkSeed z ∨ VirtualHit vp256s z ∨
              LinkedHonestInput vp256s z)) ∨
          RunItsrCovered (shakeCore vp256s) z] ∧
      (verifyingAdv vp256s (by decide) (by decide) adv).RomQueryBound
        (2 ^ 64 + GeneralScheme.verifyInternalQueryBound vp256s.params) (2 ^ 64) :=
  ⟨shakeAdvantage_pure_le_viewEvents rfl (by decide) pkSeed adv,
    romQueryBound_verifyingAdv _ _ hadv⟩

/-! ## Off a weak seed -/

/-- **At a strong seed the new events never fire.** On the support of the verifying run at
`typeSevenSeed`, no run point has a virtual hit or an honest input at a linked point. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (adv : UnforgeableAdversary
      (shakeRomScheme vp256s optRand (pure WeakKeyBoundTest.typeSevenSeed)))
    {z : RomOutcome vp256s (shakeCore vp256s) × (hashSpec (shakeCore vp256s)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp256s) (Equiv.refl _) optRand
      (pure WeakKeyBoundTest.typeSevenSeed) (verifyingAdv vp256s (by decide) (by decide) adv))) :
    ¬VirtualHit vp256s z ∧ ¬LinkedHonestInput vp256s z := by
  have hseed : z.1.pk.pkSeed = WeakKeyBoundTest.typeSevenSeed := by
    simpa using pkSeed_mem_support_of_mem_support_romSchemeRun _ optRand _ hz
  exact not_virtualHit_and_not_linkedHonestInput z
    (hseed ▸ WeakKeyBoundTest.not_isHonestKey_typeSevenSeed)

/-! ## A cached linked point is not an honest input -/

/-- Every honest entry of a cache at the oracle-backed provider rests on a settled secret, so the
cache holds a one-input tweakable-hash point. -/
private theorem exists_secret_of_honestEntry {c : PublicHash.Cache (shakeCore vp256s)}
    {s : (shakeCore vp256s).PkSeed} {sk : (shakeCore vp256s).SkSeed}
    {t : (publicHashSpec (shakeCore vp256s)).Domain}
    (h : HonestEntry (oracleSecret (shakeCore vp256s) (Equiv.refl _) s sk) s c t) :
    ∃ k y, (c (.thash s k [y])).isSome := by
  have secret : ∀ {a : Adrs} {x : (shakeCore vp256s).Y}, simulateQ c.toPartialImpl
      (oracleSecret (shakeCore vp256s) (Equiv.refl _) (m := OracleComp (publicHashSpec _)) s sk
        a) = some x → ∃ k y, (c (.thash s k [y])).isSome := fun hx =>
    ⟨_, _, Option.isSome_iff_exists.2
      ⟨_, (simulateQ_toPartialImpl_oracleSecret _ _ _ _ _ _).symm.trans hx⟩⟩
  have hfors : ∀ {adrs : Adrs} {z i : ℕ} {v : (shakeCore vp256s).Y},
      forsNodeWithSecret? (shakeCore vp256s) c (oracleSecret (shakeCore vp256s) (Equiv.refl _)
        s sk) s adrs z i = some v → ∃ k y, (c (.thash s k [y])).isSome := fun hv => by
    obtain ⟨y, hy⟩ := PerfectMerkleTree.exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _
      hv (Nat.zero_le _) (t' := _ * 2 ^ _) (Nat.mul_div_cancel _ (by positivity))
    simp only [PerfectMerkleTree.merkleRootM, forsLeafWithSecret, simulateQ_bind_eq_some_iff] at hy
    obtain ⟨x, hx, -⟩ := hy
    exact secret hx
  have htops : ∀ {adrs : Adrs} {tops : Vector (shakeCore vp256s).Y vp256s.params.len},
      wotsPkGenTopsWithSecret? (shakeCore vp256s) c (oracleSecret (shakeCore vp256s)
        (Equiv.refl _) s sk) s adrs = some tops → ∃ k y, (c (.thash s k [y])).isSome :=
    fun ht => by
      obtain ⟨x, hx, -⟩ := (wotsPkGenTopsWithSecret?_eq_some_iff _ _ _ _ _).1 ht ⟨0, by decide⟩
      exact secret hx
  cases h with
  | xmssNode adrs z i l r _ _ hl =>
    obtain ⟨y, hy⟩ := PerfectMerkleTree.exists_simulateQ_merkleRootM_eq_some_of_div_pow_eq _ _ _
      hl (Nat.zero_le _) (t' := _ * 2 ^ _) (Nat.mul_div_cancel _ (by positivity))
    simp only [PerfectMerkleTree.merkleRootM, xmssLeafWithSecret, wotsPkGenWithSecret,
      simulateQ_bind_eq_some_iff] at hy
    obtain ⟨tops, ht, -⟩ := hy
    exact htops ht
  | wotsPk _ _ _ ht => exact htops ht
  | wotsChain _ _ _ _ _ _ hx => exact secret hx
  | forsLeaf _ _ _ _ hx => exact secret hx
  | forsNode _ _ _ _ _ _ _ hl => exact hfors hl
  | forsRoots _ _ _ ht => exact hfors (ht ⟨0, by decide⟩)

/-- **The negative control.** For every run point at the public key `pk`, with secret seed other
than `PK.root` and final cache `cache`: the cache holds a linked point, and there is neither a
virtual hit nor an honest input at a linked point. -/
example (z : RomOutcome vp256s (shakeCore vp256s) × (hashSpec (shakeCore vp256s)).QueryCache)
    (hpk : z.1.pk = pk) (hsk : z.1.sk.skSeed ≠ pk.pkRoot) (hc : z.2 = cache) :
    LinkedCached vp256s z.1.pk z.2 ∧ ¬VirtualHit vp256s z ∧ ¬LinkedHonestInput vp256s z := by
  have hno : ∀ t, ¬HonestEntry (oracleSecret (shakeCore vp256s) (Equiv.refl _) z.1.pk.pkSeed
      z.1.sk.skSeed) z.1.pk.pkSeed z.2.fst t := fun t ht => by
    obtain ⟨k, y, hk⟩ := exists_secret_of_honestEntry ht
    rw [hc, hpk, QueryCache.fst_apply, cache_apply_of_ne (fun h => List.cons_ne_nil _ _
      (List.cons.inj (PublicHashQuery.thash.inj (Sum.inl_injective h)).2.2).2.symm) (by simp)] at hk
    cases hk
  refine ⟨⟨.thash pk.pkSeed weakKey [pk.pkRoot, node], ?_, ?_⟩,
    fun ⟨_, _, _, _, _, h, _⟩ => hno _ h, ?_⟩
  · rw [hpk]
    exact ⟨rfl, rfl, rfl⟩
  · rw [hc, cache, QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.cacheQuery_self]
    rfl
  rintro (⟨t, -, ht⟩ | ⟨-, -, -, -, -, -, hr⟩)
  · exact hno t ht
  · exact hsk (by rw [← hpk]; exact hr)

end SLHDSA.ByteLinkedViewTest
