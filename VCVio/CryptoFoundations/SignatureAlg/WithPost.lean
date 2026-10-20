/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# An unforgeability adversary followed by a program on its output

`SignatureAlg.UnforgeableAdversary.withPost adv post` runs the adversary `adv` and then, as its own
queries to the ambient oracles, the program `post pk out` on its public key `pk` and its output
`out`; it discards the program's result and outputs `out`. A reduction uses it to make the
adversary perform computations, a verification of its own forgery for instance, whose queries the
experiment then records like any other query of the adversary.

* `SignatureAlg.UnforgeableAdversary.RomQueryBound.withPost`: in the random oracle model the
  budget adds up. If `adv` makes at most `qh` hash and `qs` signing queries and every
  `post pk out` at most `v` hash queries, the adversary followed by `post` makes at most `qh + v`
  hash and `qs` signing queries.
-/

public section

open OracleSpec OracleComp

namespace SignatureAlg

variable {ι : Type} {M PK SK S : Type}

/-- The adversary that runs `adv` and then the program `post pk out` on its public key `pk` and
its output `out`, as its own queries to the ambient oracles; its output is that of `adv`. -/
@[expose] def UnforgeableAdversary.withPost {spec : OracleSpec ι}
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg)
    {β : Type} (post : PK → M × S → OracleComp spec β) : UnforgeableAdversary sigAlg where
  main pk := do
    let out ← adv.main pk
    let _ ← liftComp (post pk out) (spec + (M →ₒ S))
    pure out

/-- **The budget of an adversary followed by a program.** If `adv` makes at most `qh` hash and
`qs` signing queries and every `post pk out` at most `v` hash queries, then `adv` followed by
`post` makes at most `qh + v` hash and `qs` signing queries. -/
theorem UnforgeableAdversary.RomQueryBound.withPost {hs : OracleSpec ι}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {adv : UnforgeableAdversary sigAlg} {qh qs v : ℕ} (hadv : adv.RomQueryBound qh qs)
    {β : Type} {post : PK → M × S → OracleComp (unifSpec + hs) β}
    (hpost : ∀ pk out, IsQueryBoundP (post pk out) (fun t => t.isRight) v) :
    (adv.withPost post).RomQueryBound (qh + v) qs := by
  intro pk
  obtain ⟨hh, hsq⟩ := hadv pk
  have hhash : ∀ t : (unifSpec + hs).Domain,
      t.isRight ↔ IsHashQuery (hs := hs) (M := M) (S := S) (.inl t) := by
    rintro (n | t) <;> simp [IsHashQuery]
  have hsign : ∀ t : (unifSpec + hs).Domain,
      False ↔ IsSignQuery (hs := hs) (M := M) (S := S) (.inl t) := by
    rintro (n | t) <;> simp [IsSignQuery]
  refine ⟨isQueryBoundP_bind hh fun out _ => ?_, (isQueryBoundP_bind hsq fun out _ => ?_).mono
    (Nat.add_zero qs).le⟩
  · exact (isQueryBoundP_bind ((hpost pk out).liftComp_subSpec hhash)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (Nat.add_zero v).le
  · exact isQueryBoundP_bind ((isQueryBoundP_false (post pk out) 0).liftComp_subSpec hsign)
      fun _ _ => isQueryBoundP_pure _ _ 0

end SignatureAlg
