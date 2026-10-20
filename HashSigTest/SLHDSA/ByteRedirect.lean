/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteRedirect
public import HashSig.SLHDSA.Security.ByteConformance

/-!
# The linked redirect, checked

`HashSig.SLHDSA.Security.ByteRedirect` redirects the tweakable-hash queries whose SHAKE256 layout
is also that of an `H_msg` query. This file checks it.

* **At SLH-DSA-SHAKE-256s** (`n = 32`) a concrete point is linked, and the redirect is not the
  identity there: the view, through the redirect, of the cache holding only that point has no entry
  at it. The string laying it out is linked and is issued as its `H_msg` query.
* **At SLH-DSA-SHAKE-128s** (`n = 16`) the redirect is the identity, every cache is its own view
  through it, no string is linked, and the forger-side redirect is the plain lift of raw queries.
* **At all 12 FIPS 205 parameter sets**: invisibility over the single oracle, the verification
  identity, and the budget of the verifying adversary.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteRedirectTest

open Concrete Security

/-- SLH-DSA-SHAKE-256s. -/
abbrev vp256s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256s

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-! ## A linked point at SLH-DSA-SHAKE-256s -/

/-- A public key: seed of bytes `0, 1, …, 31`, root of bytes `7`. -/
def pk : PublicKeyCore (shakeCore vp256s) :=
  ⟨(Vector.ofFn fun i => (i.val.toUInt8 : Byte) : Bytes 32), (Vector.replicate 32 7 : Bytes 32)⟩

/-- The address key with the bytes of the public seed. -/
def seedKey : (shakeCore vp256s).AdrsKey :=
  (Vector.ofFn fun i => (i.val.toUInt8 : Byte) : Bytes 32)

/-- A node. -/
def node : (shakeCore vp256s).Y := (Vector.replicate 32 9 : Bytes 32)

/-- The tweakable-hash query `T(PK.seed, PK.seed, [PK.root, node])`. -/
abbrev linkedPoint : (publicHashSpec (shakeCore vp256s)).Domain :=
  .thash pk.pkSeed seedKey [pk.pkRoot, node]

/-- It is linked. -/
theorem isLinked_linkedPoint : IsLinked vp256s pk linkedPoint := ⟨rfl, rfl, rfl⟩

/-- The cache holding the node `node` at the linked point and nothing else. -/
noncomputable def cache : (publicHashSpec (shakeCore vp256s)).QueryCache :=
  (∅ : (publicHashSpec (shakeCore vp256s)).QueryCache).cacheQuery linkedPoint node

/-- The view of the cache through the redirect has no entry at the linked point, where the cache
has one. -/
theorem viewBy_cache_linkedPoint :
    cache.viewBy (linkedRedirect vp256s pk) linkedPoint = none ∧
      cache linkedPoint = some node := by
  refine ⟨?_, QueryCache.cacheQuery_self _ _ _⟩
  rw [viewBy_linkedRedirect_of_isLinked cache isLinked_linkedPoint]
  change Option.map (prefixBytes 32) (cache (linkedHmsg vp256s pk.pkSeed pk.pkRoot [node])) =
    (none : Option (Bytes 32))
  simp [cache, QueryCache.cacheQuery_of_ne]

/-- **The redirect is not the identity at SLH-DSA-SHAKE-256s.** -/
theorem linkedRedirect_linkedPoint_ne :
    linkedRedirect vp256s pk linkedPoint ≠ query linkedPoint := fun h => by
  have := viewBy_cache_linkedPoint
  rw [QueryCache.viewBy_apply_of_eq_query h] at this
  simp [this.2] at this

/-- The string laying out the linked point is linked. -/
theorem isLinkedString_encode :
    IsLinkedString vp256s pk (encode vp256s (.inl linkedPoint)) :=
  ⟨_, isLinked_linkedPoint, rfl⟩

/-- The forger-side redirect issues that string as the `H_msg` query it lays out. -/
example : linkedRawImpl vp256s pk (.inr (encode vp256s (.inl linkedPoint))) =
    (query (spec := unifSpec + (hashSpec (shakeCore vp256s) + shakeSpec vp256s))
      (.inr (.inl (.inl (.hmsg pk.pkSeed pk.pkSeed pk.pkRoot
        ((encode vp256s (.inl linkedPoint)).drop 96))))) :
      OracleComp (unifSpec + (hashSpec (shakeCore vp256s) + shakeSpec vp256s))
        (Bytes vp256s.params.m)) := by
  simp only [linkedRawImpl, isLinkedString_encode, ↓reduceIte]
  rfl

/-! ## The identity at SLH-DSA-SHAKE-128s -/

/-- The redirect passes every query on. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (t : (publicHashSpec (shakeCore vp128s)).Domain) :
    linkedRedirect vp128s pk t = query t :=
  linkedRedirect_eq_query_of_ne (by decide) t

/-- Every cache is its own view through the redirect. -/
example (pk : PublicKeyCore (shakeCore vp128s))
    (c : (publicHashSpec (shakeCore vp128s)).QueryCache) :
    c.viewBy (linkedRedirect vp128s pk) = c :=
  QueryCache.ext fun t =>
    QueryCache.viewBy_apply_of_eq_query (linkedRedirect_eq_query_of_ne (by decide) t) c

/-- No string is linked. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (x : List Byte) : ¬IsLinkedString vp128s pk x :=
  not_isLinkedString_of_ne (by decide) x

/-- The forger-side redirect is the plain lift of raw queries. -/
example (pk : PublicKeyCore (shakeCore vp128s)) :
    linkedRawImpl vp128s pk = liftRawImpl (hs := hashSpec (shakeCore vp128s)) :=
  linkedRawImpl_eq_liftRawImpl_of_ne (by decide)

/-! ## At all 12 FIPS 205 parameter sets -/

/-- The redirect is invisible over the single oracle. -/
example (set : FipsParameterSet) (pk : PublicKeyCore (shakeCore set.validatedParams)) {α : Type}
    (oa : OracleComp (unifSpec + hashSpec (shakeCore set.validatedParams)) α) :
    simulateQ (encImpl _) (simulateQ (linkedHashRedirect _ pk) oa) = simulateQ (encImpl _) oa :=
  simulateQ_encImpl_simulateQ_linkedHashRedirect oa

/-- The single-SHAKE256 verification is the redirected verification, encoded. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed)
    (pk : PublicKeyCore (shakeCore set.validatedParams)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore set.validatedParams (shakeCore set.validatedParams)) :
    (shakeRomScheme _ optRand pkSeedDist).verify pk msg sig =
      simulateQ (encImpl _) (liftPub _ (redirectedVerify _ pk msg sig)) :=
  shakeRomScheme_verify_eq optRand pkSeedDist msg sig

/-- Encoding the common interface undoes the forger-side redirect. -/
example (set : FipsParameterSet) (pk : PublicKeyCore (shakeCore set.validatedParams))
    (pkSeed : (shakeCore set.validatedParams).PkSeed) :
    (shakeEncoding _ set.n_le_32 set.n_le_m pkSeed).encodeImpl ∘ₛ linkedRawImpl _ pk =
      QueryImpl.id' _ :=
  encodeImpl_shakeEncoding_compose_linkedRawImpl set.n_le_32 set.n_le_m pkSeed

/-- The verifying adversary makes at most `qh + V` hash and `qs` signing queries. -/
example (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    {pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    (verifyingAdv _ set.n_le_32 set.n_le_m adv).RomQueryBound
      (qh + GeneralScheme.verifyInternalQueryBound set.validatedParams.params) qs :=
  romQueryBound_verifyingAdv set.n_le_32 set.n_le_m hadv

end SLHDSA.ByteRedirectTest
