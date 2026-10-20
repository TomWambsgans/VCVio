/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomSchemeRun

/-!
# The random-oracle bad-event bridge for SLH-DSA with both PRFs inside the oracle

A cache on which key generation, every logged signature and the forgery's accepting
verification replay exhibits one of the three events of `HashSig.SLHDSA.Security.RomDescentSecret`:
a same-address target collision, a hidden-value hit or interleaved-target coverage
(`bad_event_of_settled`).  On the support of `romSchemeRun` the final cache settles all three
replays at the run's own provider `oracleSecret core e o.pk.pkSeed o.sk.skSeed` and public seed,
so a winning forgery exhibits one of the three events there, each conjoined with freshness of the
forged message for the signing log (`bad_event_of_wins_romSchemeRun`).  The provider and the seed
are fixed by the run, not chosen by the caller.

The descent runs top-down from the cached public root: key generation settles the honest root of
the top tree at the value the forgery's verification recovers there, `xmssLayer_cases`
moves the descent one layer down for as long as the used leaf's honest message is the one the
verification presents, and `fors_cases` closes it at layer `0`.  Two facts feed it:
`exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret` reads the honest per-layer
signing walk (FIPS 205 Algorithm 12) off the cache, and
`exists_honestMessage?_eq_some_of_usedLeaf` settles the honest message at every leaf a logged
signature used.

## Scope

* Everything here is deterministic: no probability is bounded, and no query budget appears.
* Coverage cannot be dropped: a fresh message whose digest selects a FORS instance and indices
  all revealed by logged signatures there is forged, with no collision and no hit, from the
  revealed FORS values and a logged hypertree signature for that instance.
* Freshness of the forged message enters no step of the descent; it is conjoined to each disjunct
  so that a union bound over the conclusion is conditioned term by term, and it is what makes the
  coverage disjunct nontrivial: replaying a logged signature on its own message covers every
  coordinate of its digest.
* Nothing here is quantum.

## Labels

*The honest signing walk*: `exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret`.

*A used leaf's honest message*: `exists_honestMessage?_eq_some_of_usedLeaf`.

*The bridge on a settled cache*: `bad_event_of_settled`.

*The bridge on the run*: `bad_event_of_wins_romSchemeRun`.

## References

- NIST FIPS 205, §7.1--§7.2 and §9.2--§9.3, Algorithms 12, 19 and 20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec GeneralHypertree SignatureAlg CanonicalGames

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The honest signing walk -/

/-- From a settled Algorithm 12 run over a provider, started at the layer-`n` position with
`layers` layers left, every layer `j ≥ n` has a settled XMSS signature over the provider at the
layer-`j` position on some message, and below the top layer the signer's own recovery of the root
from it is settled. -/
theorem exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret
    (c : PublicHash.Cache core) (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (pk : core.PkSeed) (parts : DigestParts vp.params) :
    ∀ (layers n : ℕ) (hnl : n + layers = vp.params.d) (hl : 0 < layers) (msg : core.Y)
      {sigs : Vector (XmssSig vp.params core) layers},
      simulateQ c.toPartialImpl (signFromPositionWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) secret false
        (LayerPosition.atLayer vp parts ⟨n, by omega⟩) layers (by simp; omega) msg) =
          some sigs →
      ∀ j : Fin vp.params.d, n ≤ j.val → ∃ (m : core.Y) (sig : XmssSig vp.params core),
        simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
          (PublicHash.tl core pk) (PublicHash.h core pk) secret m
          (LayerPosition.atLayer vp parts j).toAdrs
          (LayerPosition.atLayer vp parts j).leaf.val) = some sig ∧
        (j.val + 1 < vp.params.d → ∃ r, xmssPkFromSig? core c
          (LayerPosition.atLayer vp parts j).leaf.val sig m pk
          (LayerPosition.atLayer vp parts j).toAdrs = some r) := by
  intro layers
  induction layers with
  | zero => intro _ _ hl; omega
  | succ k ih =>
    intro n hnl _ msg sigs hsign j hj
    cases k with
    | zero =>
      rw [simulateQ_toPartialImpl_signFromPositionWithSecret_one_false_eq_some_iff] at hsign
      obtain ⟨sig, hsig, -⟩ := hsign
      obtain ⟨jv, hjlt⟩ := j
      obtain rfl : jv = n := by simp at hj; omega
      exact ⟨msg, sig, hsig, fun h => by omega⟩
    | succ k =>
      obtain ⟨sig, root, rest, hsig, hrec, hrest, -⟩ :=
        (simulateQ_toPartialImpl_signFromPositionWithSecret_add_two_eq_some_iff core c secret pk
          false _ k _ msg).mp hsign
      rcases Nat.eq_or_lt_of_le hj with hjn | hjn
      · obtain ⟨jv, hjlt⟩ := j
        simp only at hjn
        subst hjn
        exact ⟨msg, sig, hsig, fun _ => ⟨root, hrec⟩⟩
      · have hrest' : simulateQ c.toPartialImpl (signFromPositionWithSecret core
            (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) secret false
            (LayerPosition.atLayer vp parts ⟨n + 1, by omega⟩) (k + 1) (by simp; omega) root) =
              some rest := by
          have hnext := LayerPosition.atLayer_succ_eq_next vp parts ⟨n, by omega⟩
            (by simp; omega)
          simp only at hnext
          rw [signFromPositionWithSecret_pos_congr secret c pk false hnext]
          exact hrest
        exact ih (n + 1) (by omega) (Nat.succ_pos k) root hrest' j hjn

/-! ## A used leaf's honest message -/

/-- If every logged signature of `o` replays on `c` at its own randomizer, a used leaf's honest
message is settled: the logged signature that passes through `pos` signed there the root its own
lower-layer XMSS signature recovers, which its settled signing replay identifies with the settled
honest root of the child tree; at layer `0` it signed the FORS public key its own recovery
produced, which the same replay identifies with the settled honest FORS public key. -/
theorem exists_honestMessage?_eq_some_of_usedLeaf
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    (hlog : ∀ x ∈ o.log, simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    (j : Fin vp.params.d) (pos : LayerPosition vp) (hused : UsedLeaf o c j pos) :
    ∃ m, honestMessage? c secret o.pk.pkSeed pos = some m := by
  obtain ⟨x, hx, digest, hd, rfl⟩ := hused
  obtain ⟨-, digest', forsPk, hd', hfs, hfp, hht⟩ :=
    components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM core c _ _ _ _ _
      (hlog x hx)
  obtain rfl : digest = digest' := Option.some.inj (hd.symm.trans hd')
  set parts := splitDigest vp.params digest
  unfold honestMessage?
  split_ifs with h0
  · obtain rfl : j = ⟨0, vp.valid.d_pos⟩ := Fin.ext (by simpa using h0)
    rw [LayerPosition.atLayer_zero_eq_initial, forsInstanceAdrs_initial]
    exact ⟨forsPk, forsPkGenWithSecret?_eq_some_of_forsSignWithSecret core c _ _ _ _ hfs hfp⟩
  · obtain ⟨jv, hjlt⟩ := j
    simp only [LayerPosition.atLayer_layer_val] at h0
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hd1 : (vp.params.d == 1) = false := by simp; omega
    simp only [GeneralHypertree.signWithSecretM, GeneralHypertree.signWithSecret, hd1] at hht
    obtain ⟨m, sig, hsign, hrec⟩ := exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret
      c _ _ parts vp.params.d 0 (by simp) vp.valid.d_pos forsPk hht ⟨j', by omega⟩
      (Nat.zero_le _)
    obtain ⟨r, hr⟩ := hrec (by omega)
    refine ⟨r, ?_⟩
    rw [LayerPosition.atLayer_succ_eq_next vp parts ⟨j', by omega⟩ (by simpa using hjlt),
      childTreeAdrs_next]
    exact xmssRootWithSecret?_eq_some_of_xmssSignWithSecret core c _ m _ _ _ hsign
      (LayerPosition.atLayer vp parts ⟨j', by omega⟩).leaf.isLt hr

/-! ## The bridge on a settled cache -/

/-- **The random-oracle bad-event bridge on a settled cache.**  If key generation at `secret`
replays on `c` to the public root of `o`, every logged signature of `o` replays on `c` at its own
randomizer, and the verification of the forgery replays on `c` to `true`, then `c` exhibits a
same-address target collision, or a hidden-value hit, or interleaved-target coverage. -/
theorem bad_event_of_settled [DecidableEq core.Y] (laws : core.ByteLaws)
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    (hroot : simulateQ c.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM core secret o.pk.pkSeed) = some o.pk.pkRoot)
    (hlog : ∀ x ∈ o.log, simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    (hver : simulateQ c.toPartialImpl
      (GeneralScheme.verifyInternalM vp core o.msg o.sig o.pk) = some true) :
    TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨ ItsrCovered o c := by
  rw [simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff] at hver
  obtain ⟨digest, forsPk, hd, hfors, hpk⟩ := hver
  rw [simulateQ_toPartialImpl_pkFromSigM_eq] at hpk
  set parts := splitDigest vp.params digest
  have hlayers := forgerLayers_of_recoverFromPositionM c o.pk.pkSeed parts o.sig.hypertree
    forsPk vp.params.d 0 (by simp) vp.valid.d_pos forsPk o.sig.hypertree rfl
    (fun k hk => by simp) hpk
  have hstep : ∀ (j : Fin vp.params.d) (m r : core.Y),
      forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk j j.isLt = some m →
      xmssPkFromSig? core c (LayerPosition.atLayer vp parts j).leaf.val o.sig.hypertree[j] m
        o.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs = some r →
      xmssRootWithSecret? core c secret o.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs =
        some r →
      TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨
        honestMessage? c secret o.pk.pkSeed (LayerPosition.atLayer vp parts j) = some m := by
    intro j m r hm hf hh
    exact (xmssLayer_cases secret laws o c j _ m ⟨digest, forsPk, hd, hfors, rfl, hm⟩
      hf hh (exists_honestMessage?_eq_some_of_usedLeaf secret o c hlog j _)).imp id
      (Or.imp id And.right)
  have bind3 : ∀ {P Q : Prop}, (TargetCollision secret o.pk.pkSeed c ∨
        HiddenHit secret o c ∨ P) →
      (P → TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨ Q) →
      TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨ Q :=
    fun h f => h.elim Or.inl fun h => h.elim (Or.inr ∘ Or.inl) f
  have key : ∀ (i : ℕ) (j : Fin vp.params.d), j.val + i + 1 = vp.params.d →
      TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨
        ∃ m r,
        forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk j j.isLt = some m ∧
        xmssPkFromSig? core c (LayerPosition.atLayer vp parts j).leaf.val o.sig.hypertree[j]
          m o.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs = some r ∧
        xmssRootWithSecret? core c secret o.pk.pkSeed
          (LayerPosition.atLayer vp parts j).toAdrs = some r := by
    intro i
    induction i with
    | zero =>
      intro j hj
      obtain ⟨m, r, hm, hf, hr⟩ := hlayers j (Nat.zero_le _)
      obtain rfl := hr (by omega)
      refine Or.inr (Or.inr ⟨m, _, hm, hf, ?_⟩)
      rw [LayerPosition.toAdrs_eq_layerAdrs_of_isFinal _ (by simp; omega)]
      exact hroot
    | succ i ih =>
      intro j hj
      refine bind3 (ih ⟨j.val + 1, by omega⟩ (by simp; omega)) fun ⟨m', r', hm', hf', hh'⟩ => ?_
      obtain ⟨m, r, hm, hf, -⟩ := hlayers j (Nat.zero_le _)
      have hnext : forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk (j.val + 1)
          (by omega) = some r := by
        change (forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk j.val _).bind _ =
          some r
        rw [hm, Option.bind_some]
        exact hf
      rw [hnext] at hm'
      obtain rfl := Option.some.inj hm'
      refine bind3 (hstep ⟨j.val + 1, by omega⟩ r r' hnext hf' hh') fun h => ?_
      refine Or.inr (Or.inr ⟨m, r, hm, hf, ?_⟩)
      simp only [honestMessage?, LayerPosition.atLayer_layer_val, Nat.add_one_ne_zero,
        ↓reduceIte] at h
      rwa [LayerPosition.atLayer_succ_eq_next vp parts j (by omega), childTreeAdrs_next] at h
  refine bind3 (key (vp.params.d - 1) ⟨0, vp.valid.d_pos⟩
    (by have := vp.valid.d_pos; simp; omega)) fun ⟨m, r, hm, hf, hh⟩ => ?_
  refine bind3 (hstep ⟨0, vp.valid.d_pos⟩ m r hm hf hh) fun h => ?_
  obtain rfl : forsPk = m := Option.some.inj hm
  simp only [honestMessage?, LayerPosition.atLayer_zero_eq_initial,
    LayerPosition.initial_layer_val, forsInstanceAdrs_initial, ↓reduceIte] at h
  exact fors_cases secret o c digest hd forsPk hfors h

section Run

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-! ## The bridge on the run -/

/-- **The random-oracle bad-event bridge.**  On the support of `romSchemeRun`, a winning forgery
exhibits, at the run's own oracle-backed provider and public seed and in the public-hash part of
the final cache, a same-address target collision, or a hidden-value hit, or interleaved-target
coverage, and in each case the forged message is fresh for the signing log. -/
theorem bad_event_of_wins_romSchemeRun (laws : core.ByteLaws) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    {z : RomOutcome vp core × (hashSpec core).QueryCache}
    (hz : z ∈ support (romSchemeRun core e optRand pkSeedDist adv)) (hw : z.1.wins = true) :
    (TargetCollision (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1.pk.pkSeed
        z.2.fst ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)) ∨
      (HiddenHit (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1 z.2.fst ∧
        z.1.msg ∉ z.1.log.map (fun e => e.1)) ∨
      (ItsrCovered z.1 z.2.fst ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)) := by
  obtain ⟨hfresh, hv⟩ := (UnforgeableTranscript.wins_eq_true_iff z.1).mp hw
  obtain ⟨-, -, hroot, hlog, hver⟩ :=
    settled_of_mem_support_romSchemeRun core e optRand pkSeedDist adv hz
  exact (bad_event_of_settled laws _ z.1 z.2.fst hroot hlog (hv ▸ hver)).imp (⟨·, hfresh⟩)
    (Or.imp (⟨·, hfresh⟩) (⟨·, hfresh⟩))

end Run

end SLHDSA.Security
