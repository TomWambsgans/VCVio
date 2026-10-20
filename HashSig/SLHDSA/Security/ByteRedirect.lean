/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteRouter
public import VCVio.OracleComp.QueryTracking.RandomOracle.Redirect

/-!
# Linked points of the SHAKE256 layouts and their redirect

At `n = 32` a tweakable-hash query `T(PK.seed, ADRS, [PK.root] ++ rest)` whose address is
`PK.seed` itself, read as `32` bytes, has the same FIPS 205 §11.1 byte string
`PK.seed ‖ PK.seed ‖ PK.root ‖ rest` as the `H_msg` query `H_msg(PK.seed, PK.seed, PK.root, rest)`.
Such a tweakable-hash query is *linked* at the public key (`IsLinked`). No query is linked for
`n ≠ 32` (`not_isLinked_of_ne`), since the address has `32` bytes and `PK.seed` has `n`.

## The redirect

`linkedRedirect vp pk` answers a linked tweakable-hash query by the first `n` bytes of the `H_msg`
query with the same byte string (`linkedHmsg`), and passes every other query of the public hash
on. It is a redirect of the public hash into itself, so a public-hash cache can be read through it
(`OracleSpec.QueryCache.viewBy`): at a linked point the view holds the first `n` bytes of the
cache's entry at the `H_msg` reading (`viewBy_linkedRedirect_of_isLinked`), and elsewhere the
cache's own entry (`viewBy_linkedRedirect_of_not_isLinked`). `linkedHashRedirect vp pk` is its
lift to the whole interface `unifSpec + hashSpec`, the identity on uniform draws and on
`PRF_msg`.

Over the single SHAKE256 oracle the redirect changes nothing: each redirected query is encoded as
the query itself (`encImpl_linkedHashRedirect`), so a program and its redirected form are one
program of the single oracle (`simulateQ_encImpl_simulateQ_linkedHashRedirect`). In particular
the verification of `shakeRomScheme` is the redirected verification of the three-oracle scheme,
`redirectedVerify`, encoded (`shakeRomScheme_verify_eq`).

## References

* NIST FIPS 205, §11.1 (SLH-DSA using SHAKE).
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

open Concrete

variable (vp : ValidatedParams) (pk : PublicKeyCore (shakeCore vp))

/-! ## Linked points -/

/-- **A linked point** at the public key `pk`: a tweakable-hash query at `PK.seed` whose address
key has the bytes of `PK.seed` and whose first input block is `PK.root`. -/
@[expose] def IsLinked : (publicHashSpec (shakeCore vp)).Domain → Prop
  | .thash s k (r :: _) =>
      s = pk.pkSeed ∧ Vector.toList (k : Bytes 32) = Vector.toList (s : Bytes vp.params.n) ∧
        r = pk.pkRoot
  | _ => False

instance : DecidablePred (IsLinked vp pk)
  | .thash _ _ [] => inferInstanceAs (Decidable False)
  | .thash s k (r :: _) => inferInstanceAs (Decidable ((s : Bytes vp.params.n) = pk.pkSeed ∧
      Vector.toList (k : Bytes 32) = Vector.toList (s : Bytes vp.params.n) ∧
        (r : Bytes vp.params.n) = pk.pkRoot))
  | .hmsg .. => inferInstanceAs (Decidable False)

/-- The `H_msg` query `H_msg(s, s, r, rest)` that a tweakable-hash query at `s` with first block
`r` and further blocks `rest` reads as when its address key has the bytes of `s`. -/
abbrev linkedHmsg (s : (shakeCore vp).PkSeed) (r : (shakeCore vp).Y)
    (rest : List (shakeCore vp).Y) : (publicHashSpec (shakeCore vp)).Domain :=
  .hmsg s s r (rest.map fun x : (shakeCore vp).Y => Vector.toList (x : Bytes vp.params.n)).flatten

variable {vp pk}

/-- No query is linked when `n ≠ 32`: the address key has `32` bytes and `PK.seed` has `n`. -/
theorem not_isLinked_of_ne (hn : vp.params.n ≠ 32) (t : (publicHashSpec (shakeCore vp)).Domain) :
    ¬IsLinked vp pk t := by
  rcases t with ⟨s, k, _ | ⟨r, rest⟩⟩ | _
  · exact id
  · rintro ⟨-, hk, -⟩
    exact hn ((Vector.length_toList (xs := (s : Bytes vp.params.n))).symm.trans
      ((congrArg List.length hk).symm.trans Vector.length_toList))
  · exact id

/-- A linked tweakable-hash query and its `H_msg` reading lay out the same byte string. -/
theorem encode_linkedHmsg {s : (shakeCore vp).PkSeed} {k : (shakeCore vp).AdrsKey}
    {r : (shakeCore vp).Y} (rest : List (shakeCore vp).Y)
    (hk : Vector.toList (k : Bytes 32) = Vector.toList (s : Bytes vp.params.n)) :
    encode vp (.inl (linkedHmsg vp s r rest)) = encode vp (.inl (.thash s k (r :: rest))) := by
  simp only [encode, hk, List.map_cons, List.flatten_cons, List.append_assoc]

/-! ## The redirect on the public hash -/

variable (vp pk)

/-- **The linked redirect.** A linked tweakable-hash query is answered by the first `n` bytes of
the `H_msg` query with the same byte string; every other public-hash query is passed on. -/
@[expose] def linkedRedirect :
    QueryImpl (publicHashSpec (shakeCore vp)) (OracleComp (publicHashSpec (shakeCore vp)))
  | .thash s k (r :: rest) =>
      if IsLinked vp pk (.thash s k (r :: rest)) then
        (prefixBytes vp.params.n <$> (query (spec := publicHashSpec (shakeCore vp))
          (linkedHmsg vp s r rest) : OracleComp _ (Bytes vp.params.m)) :
          OracleComp (publicHashSpec (shakeCore vp)) (shakeCore vp).Y)
      else query (spec := publicHashSpec (shakeCore vp)) (.thash s k (r :: rest))
  | t => query (spec := publicHashSpec (shakeCore vp)) t

variable {vp pk}

/-- At a linked point the redirect queries the `H_msg` reading and keeps the first `n` bytes. -/
theorem linkedRedirect_of_isLinked {s : (shakeCore vp).PkSeed} {k : (shakeCore vp).AdrsKey}
    {r : (shakeCore vp).Y} {rest : List (shakeCore vp).Y}
    (h : IsLinked vp pk (.thash s k (r :: rest))) :
    linkedRedirect vp pk (.thash s k (r :: rest)) =
      (prefixBytes vp.params.n <$> (query (spec := publicHashSpec (shakeCore vp))
        (linkedHmsg vp s r rest) : OracleComp _ (Bytes vp.params.m)) :
        OracleComp (publicHashSpec (shakeCore vp)) (shakeCore vp).Y) := by
  simp only [linkedRedirect, h, ↓reduceIte]

/-- Off the linked points the redirect passes the query on. -/
theorem linkedRedirect_of_not_isLinked {t : (publicHashSpec (shakeCore vp)).Domain}
    (h : ¬IsLinked vp pk t) : linkedRedirect vp pk t = query t := by
  rcases t with ⟨s, k, _ | ⟨r, rest⟩⟩ | _
  · rfl
  · simp only [linkedRedirect, h, ↓reduceIte]
  · rfl

/-- The redirect passes every `H_msg` query on. -/
@[simp] theorem linkedRedirect_hmsg (r : (shakeCore vp).Y) (s : (shakeCore vp).PkSeed)
    (root : (shakeCore vp).Y) (msg : List Byte) :
    linkedRedirect vp pk (.hmsg r s root msg) =
      query (spec := publicHashSpec (shakeCore vp)) (PublicHashQuery.hmsg r s root msg) := rfl

/-- For `n ≠ 32` the redirect passes every query on. -/
theorem linkedRedirect_eq_query_of_ne (hn : vp.params.n ≠ 32)
    (t : (publicHashSpec (shakeCore vp)).Domain) : linkedRedirect vp pk t = query t :=
  linkedRedirect_of_not_isLinked (not_isLinked_of_ne hn t)

/-- At a linked point, a public-hash cache read through the redirect holds the first `n` bytes of
its entry at the `H_msg` reading. -/
theorem viewBy_linkedRedirect_of_isLinked (c : (publicHashSpec (shakeCore vp)).QueryCache)
    {s : (shakeCore vp).PkSeed} {k : (shakeCore vp).AdrsKey} {r : (shakeCore vp).Y}
    {rest : List (shakeCore vp).Y} (h : IsLinked vp pk (.thash s k (r :: rest))) :
    c.viewBy (linkedRedirect vp pk) (.thash s k (r :: rest)) =
      (c (linkedHmsg vp s r rest)).map (prefixBytes vp.params.n) := by
  rw [QueryCache.viewBy_apply, linkedRedirect_of_isLinked h]
  exact (simulateQ_map _ _ _).trans
    (congrArg (prefixBytes vp.params.n <$> ·) (simulateQ_spec_query _ _))

/-- Off the linked points, a public-hash cache read through the redirect is the cache. -/
theorem viewBy_linkedRedirect_of_not_isLinked (c : (publicHashSpec (shakeCore vp)).QueryCache)
    {t : (publicHashSpec (shakeCore vp)).Domain} (h : ¬IsLinked vp pk t) :
    c.viewBy (linkedRedirect vp pk) t = c t :=
  QueryCache.viewBy_apply_of_eq_query (linkedRedirect_of_not_isLinked h) c

/-- Each redirected query is one query. -/
theorem isTotalQueryBound_linkedRedirect (t : (publicHashSpec (shakeCore vp)).Domain) :
    IsTotalQueryBound (linkedRedirect vp pk t) 1 := by
  have hq {β : Type} (t' : (publicHashSpec (shakeCore vp)).Domain)
      (f : (publicHashSpec (shakeCore vp)).Range t' → β) :
      IsTotalQueryBound (f <$> (query t' : OracleComp (publicHashSpec (shakeCore vp)) _)) 1 := by
    rw [map_eq_bind_pure_comp]
    exact isTotalQueryBound_query_bind_iff.2 ⟨Nat.one_pos, fun _ => trivial⟩
  by_cases h : IsLinked vp pk t
  · rcases t with ⟨s, k, _ | ⟨r, rest⟩⟩ | _
    · exact h.elim
    · rw [linkedRedirect_of_isLinked h]
      exact hq _ _
    · exact h.elim
  · rw [linkedRedirect_of_not_isLinked h, ← id_map (query t)]
    exact hq t id

/-! ## The redirect on the whole interface -/

variable (vp)

/-- A public-hash program as a program of the whole interface `unifSpec + hashSpec`, its queries
issued through the query capability. -/
noncomputable abbrev liftPub {α : Type} (P : OracleComp (publicHashSpec (shakeCore vp)) α) :
    OracleComp (unifSpec + hashSpec (shakeCore vp)) α :=
  simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec (shakeCore vp))
    (m := OracleComp (unifSpec + hashSpec (shakeCore vp)))) P

variable (pk)

/-- **The linked redirect on the whole interface**: `linkedRedirect` on the public hash, the
identity on uniform draws and on `PRF_msg`. -/
@[expose] noncomputable def linkedHashRedirect :
    QueryImpl (unifSpec + hashSpec (shakeCore vp))
      (OracleComp (unifSpec + hashSpec (shakeCore vp))) :=
  QueryImpl.ofLift unifSpec (OracleComp (unifSpec + hashSpec (shakeCore vp))) +
    ((HasQuery.toQueryImpl (spec := publicHashSpec (shakeCore vp))
        (m := OracleComp (unifSpec + hashSpec (shakeCore vp))) ∘ₛ linkedRedirect vp pk) +
      QueryImpl.ofLift (prfMsgSpec (shakeCore vp))
        (OracleComp (unifSpec + hashSpec (shakeCore vp))))

/-- The redirected verification of SLH-DSA at the public key `pk`: FIPS 205's Algorithm 20 over
the public hash with every query redirected by `linkedRedirect`. -/
@[expose] noncomputable def redirectedVerify (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp (shakeCore vp)) :
    OracleComp (publicHashSpec (shakeCore vp)) Bool :=
  simulateQ (linkedRedirect vp pk) (GeneralScheme.verifyInternalM vp (shakeCore vp) msg sig pk)

variable {vp pk}

/-- Redirecting a lifted public-hash program on the whole interface is lifting the redirected
program. -/
theorem simulateQ_linkedHashRedirect_liftPub {α : Type}
    (P : OracleComp (publicHashSpec (shakeCore vp)) α) :
    simulateQ (linkedHashRedirect vp pk) (liftPub vp P) =
      liftPub vp (simulateQ (linkedRedirect vp pk) P) := by
  rw [liftPub, liftPub, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  exact simulateQ_HasQuery_query _ _

/-- The redirected verification makes at most `V = verifyInternalQueryBound` queries. -/
theorem isTotalQueryBound_redirectedVerify (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp (shakeCore vp)) :
    IsTotalQueryBound (redirectedVerify vp pk msg sig)
      (GeneralScheme.verifyInternalQueryBound vp.params) := by
  have h := (GeneralScheme.verifyInternalM_isTotalQueryBound vp (shakeCore vp) msg sig
    pk).simulateQ_of_step_le (isTotalQueryBound_linkedRedirect (pk := pk))
  rwa [Nat.mul_one] at h

/-- Verification of `romScheme` is the public-hash verification, lifted. -/
theorem romScheme_verify_eq_liftPub
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp (shakeCore vp)) :
    (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).verify pk msg sig =
      liftPub vp (GeneralScheme.verifyInternalM vp (shakeCore vp) msg sig pk) :=
  (GeneralScheme.verifyInternalM_natural vp (shakeCore vp)
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec (shakeCore vp))
      (m := OracleComp (unifSpec + hashSpec (shakeCore vp)))) msg sig pk).symm

/-! ## Invisibility over the single oracle -/

/-- **The redirect is invisible over the single oracle, query by query.** -/
theorem encImpl_linkedHashRedirect (t : (unifSpec + hashSpec (shakeCore vp)).Domain) :
    simulateQ (encImpl vp) (linkedHashRedirect vp pk t) = encImpl vp t := by
  rcases t with n | (t | q)
  · exact simulateQ_HasQuery_query (encImpl vp) _
  · by_cases h : IsLinked vp pk t
    · rcases t with ⟨s, k, _ | ⟨r, rest⟩⟩ | _
      · exact h.elim
      · change simulateQ (encImpl vp) (liftPub vp (linkedRedirect vp pk _)) = _
        rw [linkedRedirect_of_isLinked h]
        simp only [liftPub]
        change prefixBytes vp.params.n <$> (query (spec := shakeSpec vp)
          (encode vp (.inl (linkedHmsg vp s r rest))) :
            OracleComp (unifSpec + shakeSpec vp) (Bytes vp.params.m)) = _
        rw [encode_linkedHmsg rest h.2.1]
        rfl
      · exact h.elim
    · change simulateQ (encImpl vp) (liftPub vp (linkedRedirect vp pk t)) = _
      rw [linkedRedirect_of_not_isLinked h]
      simp only [liftPub, simulateQ_HasQuery_query]
      exact simulateQ_HasQuery_query (encImpl vp) _
  · exact simulateQ_HasQuery_query (encImpl vp) _

/-- **The redirect is invisible over the single oracle, program by program.** Encoding a program
of the whole interface with its queries redirected is encoding the program. -/
theorem simulateQ_encImpl_simulateQ_linkedHashRedirect {α : Type}
    (oa : OracleComp (unifSpec + hashSpec (shakeCore vp)) α) :
    simulateQ (encImpl vp) (simulateQ (linkedHashRedirect vp pk) oa) =
      simulateQ (encImpl vp) oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply encImpl_linkedHashRedirect oa

/-- **The single-SHAKE256 verification is the redirected verification, encoded.** -/
theorem shakeRomScheme_verify_eq
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp (shakeCore vp)) :
    (shakeRomScheme vp optRand pkSeedDist).verify pk msg sig =
      simulateQ (encImpl vp) (liftPub vp (redirectedVerify vp pk msg sig)) := by
  rw [redirectedVerify, ← simulateQ_linkedHashRedirect_liftPub,
    simulateQ_encImpl_simulateQ_linkedHashRedirect,
    ← romScheme_verify_eq_liftPub optRand pkSeedDist]
  rfl

end SLHDSA.Security
