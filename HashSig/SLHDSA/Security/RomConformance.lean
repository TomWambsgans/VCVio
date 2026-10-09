/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CacheSecret

/-!
# The random-oracle scheme at a deterministic primitive bundle

A secret provider of `HashSig.SLHDSA.SecretProvider` is honest when it returns
`PRF(PK.seed, SK.seed, ADRS)` at every address: `prfSecret core pkSeed skSeed`. This module proves
that each provider-parametric twin at the honest provider is the landed FIPS 205 program it twins,
at every lawful monad, and uses that to identify `romScheme` with FIPS 205's internal algorithms
once its three oracles are answered by a deterministic primitive bundle.

## Main definitions

* `prfSecret core pkSeed skSeed`: the honest provider, `pure ∘ core.PRF pkSeed skSeed`.
* `Security.romAnswer prims`: the answer function of `hashSpec prims.core` given by a bundle: the
  tweakable hash and `H_msg` by `PublicHash.impl prims`, `PRF_msg` by `prims.PRFmsg`.
* `Security.internalAlg vp prims optRand pkSeedDist`: FIPS 205 Algorithms 18–20 as a signature
  scheme over `ProbComp`, built from `GeneralScheme.keygenInternal`, `signInternal` and
  `verifyInternal`, with the public seed drawn from `pkSeedDist`, the secret seeds uniformly, and
  `opt_rand` from `optRand`.

## Main statements

* `keygenInternalWithSecretM_prfSecret`, `signInternalWithSecretRandomizerM_prfSecret`: the
  scheme twins at the honest provider are `GeneralHypertree.rootM` and
  `GeneralScheme.signInternalWithRandomizerM`.
* `Security.romScheme_map_romAnswer`: when the tweakable hash of `prims` at a secret-key address
  applied to `e SK.seed` is `prims.PRF`, answering the oracles of `romScheme prims.core e` by
  `romAnswer prims` gives `internalAlg vp prims`.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA

section PrfSecret

variable {p : Params} (core : CorePrimitives p)

/-- The honest secret provider: the WOTS+ or FORS secret value at an address is
`PRF(PK.seed, SK.seed, ADRS)`, returned without effect. -/
@[expose] def prfSecret {m : Type → Type*} [Monad m] (pkSeed : core.PkSeed)
    (skSeed : core.SkSeed) : Adrs → m core.Y :=
  fun a => pure (core.PRF pkSeed skSeed a)

variable {m : Type → Type*} [Monad m] [LawfulMonad m]
  (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
  (nodeHash : Adrs → core.Y → core.Y → m core.Y) (pkSeed : core.PkSeed) (skSeed : core.SkSeed)

/-- The WOTS+ chain ends at the honest provider are the landed ones. -/
theorem wotsPkGenTopsWithSecret_prfSecret (adrs : Adrs) :
    wotsPkGenTopsWithSecret core hash (prfSecret core pkSeed skSeed) adrs =
      wotsPkGenTopsWith core hash skSeed pkSeed adrs := by
  simp only [wotsPkGenTopsWithSecret, wotsPkGenTopsWith, prfSecret, pure_bind]

/-- The WOTS+ signature at the honest provider is the landed one. -/
theorem wotsSignWithSecret_prfSecret (msg : core.Y) (adrs : Adrs) :
    wotsSignWithSecret core hash (prfSecret core pkSeed skSeed) msg adrs =
      wotsSignWith core hash msg skSeed pkSeed adrs := by
  simp only [wotsSignWithSecret, wotsSignWith, prfSecret, pure_bind]

/-- The WOTS+ public key at the honest provider is the landed one. -/
theorem wotsPkGenWithSecret_prfSecret (adrs : Adrs) :
    wotsPkGenWithSecret core hash compress (prfSecret core pkSeed skSeed) adrs =
      wotsPkGenWith core hash compress skSeed pkSeed adrs := by
  rw [wotsPkGenWithSecret, wotsPkGenWith, wotsPkGenTopsWithSecret_prfSecret]

/-- The XMSS leaves at the honest provider are the landed ones. -/
theorem xmssLeafWithSecret_prfSecret (adrs : Adrs) :
    xmssLeafWithSecret core hash compress (prfSecret core pkSeed skSeed) adrs =
      xmssLeafWith core hash compress skSeed pkSeed adrs := by
  funext t
  exact wotsPkGenWithSecret_prfSecret core hash compress pkSeed skSeed _

/-- The XMSS subtree roots at the honest provider are the landed ones. -/
theorem xmssNodeWithSecret_prfSecret (adrs : Adrs) (z t : ℕ) :
    xmssNodeWithSecret core hash compress nodeHash (prfSecret core pkSeed skSeed) adrs z t =
      xmssNodeWith core hash compress nodeHash skSeed pkSeed adrs z t := by
  rw [xmssNodeWithSecret, xmssNodeWith, xmssLeafWithSecret_prfSecret]

/-- The XMSS tree root at the honest provider is the landed one. -/
theorem xmssRootWithSecret_prfSecret (adrs : Adrs) :
    xmssRootWithSecret core hash compress nodeHash (prfSecret core pkSeed skSeed) adrs =
      xmssRootWith core hash compress nodeHash skSeed pkSeed adrs :=
  xmssNodeWithSecret_prfSecret core hash compress nodeHash pkSeed skSeed adrs _ _

/-- The XMSS signature at the honest provider is the landed one. -/
theorem xmssSignWithSecret_prfSecret (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    xmssSignWithSecret core hash compress nodeHash (prfSecret core pkSeed skSeed) msg adrs idx =
      xmssSignWith core hash compress nodeHash msg skSeed pkSeed adrs idx := by
  rw [xmssSignWithSecret, xmssSignWith, xmssLeafWithSecret_prfSecret,
    wotsSignWithSecret_prfSecret]

/-- The FORS leaves at the honest provider are the landed ones. -/
theorem forsLeafWithSecret_prfSecret (adrs : Adrs) :
    forsLeafWithSecret core hash (prfSecret core pkSeed skSeed) adrs =
      forsLeafWith core hash skSeed pkSeed adrs := by
  funext t
  simp only [forsLeafWithSecret, forsLeafWith, forsSkGenCore, prfSecret, pure_bind]

/-- The FORS signature at the honest provider is the landed one. -/
theorem forsSignWithSecret_prfSecret (md : List Byte) (adrs : Adrs) :
    forsSignWithSecret core hash nodeHash (prfSecret core pkSeed skSeed) md adrs =
      forsSignWith core hash nodeHash md skSeed pkSeed adrs := by
  simp only [forsSignWithSecret, forsSignWith, forsLeafWithSecret_prfSecret, forsSkGenCore,
    prfSecret, pure_bind]

end PrfSecret

namespace GeneralHypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  {m : Type → Type*} [Monad m] [LawfulMonad m]
  (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
  (nodeHash : Adrs → core.Y → core.Y → m core.Y) (pkSeed : core.PkSeed) (skSeed : core.SkSeed)

/-- Hypertree signing from a position at the honest provider is the landed loop. -/
theorem signFromPositionWithSecret_prfSecret (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      signFromPositionWithSecret core hash compress nodeHash (prfSecret core pkSeed skSeed)
          recoverFinal pos layers h msg =
        signFromPositionWith vp core hash compress nodeHash skSeed pkSeed recoverFinal pos
          layers h msg
  | 0, _, _ => by rw [signFromPositionWithSecret, signFromPositionWith]
  | 1, _, msg => by
      rw [signFromPositionWithSecret, signFromPositionWith, xmssSignWithSecret_prfSecret]
  | layers + 2, hremaining, msg => by
      rw [signFromPositionWithSecret, signFromPositionWith, xmssSignWithSecret_prfSecret]
      refine bind_congr fun sig => bind_congr fun root => ?_
      dsimp only
      rw [signFromPositionWithSecret_prfSecret false _ (layers + 1)]

/-- Hypertree signing at the honest provider is the landed signer. -/
theorem signWithSecret_prfSecret (msg : core.Y) (parts : DigestParts vp.params) :
    signWithSecret core hash compress nodeHash (prfSecret core pkSeed skSeed) msg parts =
      signWith vp core hash compress nodeHash msg skSeed pkSeed parts :=
  signFromPositionWithSecret_prfSecret core hash compress nodeHash pkSeed skSeed _ _ _ _ _

/-- The hypertree root at the honest provider is the landed root. -/
theorem rootWithSecret_prfSecret :
    rootWithSecret core hash compress nodeHash (prfSecret core pkSeed skSeed) =
      rootWith vp core hash compress nodeHash skSeed pkSeed :=
  xmssRootWithSecret_prfSecret core hash compress nodeHash pkSeed skSeed _

end GeneralHypertree

namespace GeneralScheme

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  {m : Type → Type*} [Monad m] [LawfulMonad m] [HasQuery (publicHashSpec core) m]
  (pkSeed : core.PkSeed) (skSeed : core.SkSeed)

/-- Key generation at the honest provider computes the landed hypertree root. -/
theorem keygenInternalWithSecretM_prfSecret :
    (keygenInternalWithSecretM core (prfSecret core pkSeed skSeed) pkSeed : m core.Y) =
      GeneralHypertree.rootM vp core skSeed pkSeed :=
  GeneralHypertree.rootWithSecret_prfSecret core _ _ _ pkSeed skSeed

/-- Signing at the honest provider and a supplied randomizer is the landed signer at that
randomizer. -/
theorem signInternalWithSecretRandomizerM_prfSecret (msg : List Byte) (pkRoot R : core.Y) :
    (signInternalWithSecretRandomizerM core (prfSecret core pkSeed skSeed) msg pkSeed pkRoot R :
        m (SignatureCore vp core)) =
      signInternalWithRandomizerM vp core msg skSeed pkSeed pkRoot R := by
  simp only [signInternalWithSecretRandomizerM, signInternalWithRandomizerM,
    forsSignWithSecretM, forsSignM, forsSignWithSecret_prfSecret,
    GeneralHypertree.signWithSecretM, GeneralHypertree.signM,
    GeneralHypertree.signWithSecret_prfSecret, GeneralHypertree.signWith,
    GeneralHypertree.signFromPositionM]

end GeneralScheme

end SLHDSA

namespace SLHDSA.Security

variable {vp : ValidatedParams}

/-- The answer function of the random-oracle interface given by a deterministic primitive
bundle: the tweakable hash and `H_msg` by `PublicHash.impl prims`, and `PRF_msg` by
`prims.PRFmsg`. -/
@[expose] def romAnswer (prims : Primitives vp.params) : QueryImpl (hashSpec prims.core) Id
  | .inl q => PublicHash.impl prims q
  | .inr q => prims.PRFmsg q.skPrf q.optRand q.msg

/-- **FIPS 205 Algorithms 18–20 as a signature scheme.** Key generation draws the public seed
from `pkSeedDist` and the two secret seeds uniformly and returns
`GeneralScheme.keygenInternal`; signing draws `opt_rand` from `optRand` and returns
`GeneralScheme.signInternal`; verification is `GeneralScheme.verifyInternal`. -/
@[expose] noncomputable def internalAlg (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (GeneralScheme.SignatureCore vp prims.core) where
  keygen := do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)
  sign pk sk msg := do
    let addrnd ← optRand pk
    pure (GeneralScheme.signInternal vp prims msg sk addrnd)
  verify pk msg sig := pure (GeneralScheme.verifyInternal vp prims msg sig pk)

section Conformance

variable (prims : Primitives vp.params) [SampleableType prims.SkSeed]
  [SampleableType prims.SkPrf] [DecidableEq prims.Y]

/-- **The random-oracle scheme at a deterministic bundle is FIPS 205.** If the tweakable hash of
`prims` at every secret-key address, applied to the secret seed read as a node through `e`, is
`prims.PRF`, then answering the oracles of `romScheme prims.core e` by `romAnswer prims` and
keeping its uniform draws gives `internalAlg vp prims`, for every `opt_rand` source and every
public-seed distribution. -/
theorem romScheme_map_romAnswer (e : prims.SkSeed ≃ prims.Y)
    (hprf : ∀ pkSeed skSeed (a : Adrs), a.IsSecretKey →
      prims.Thash pkSeed (prims.adrsToKey a) [e skSeed] = prims.PRF pkSeed skSeed a)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (romScheme prims.core e optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      internalAlg vp prims optRand pkSeedDist := by
  let _ : HasQuery (publicHashSpec prims.core) ProbComp :=
    ⟨fun q => liftM (PublicHash.impl prims q)⟩
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + hashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (unifFwdAnswerImpl (romAnswer prims))
      map_query' := fun q => by
        simp [unifFwdAnswerImpl, romAnswer] }
  have hLift : ∀ {α : Type} (oa : ProbComp α),
      F.toMonadHom (liftM oa : OracleComp (unifSpec + hashSpec prims.core) α) = oa := by
    intro α oa
    change simulateQ (unifFwdAnswerImpl (romAnswer prims)) _ = oa
    rw [unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
      QueryImpl.liftTarget_self, simulateQ_id']
  have hFree : ∀ {α : Type} (oa : OracleComp (publicHashSpec prims.core) α),
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := ProbComp)).toMonadHom oa = pure (simulateQ (PublicHash.impl prims) oa) := by
    intro α oa
    have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp) =
        (PublicHash.impl prims).liftTarget ProbComp := by
      funext q
      rfl
    rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  have hSecret : ∀ pkSeed skSeed (a : Adrs), a.IsSecretKey →
      F.toMonadHom (oracleSecret prims.core e pkSeed skSeed a) =
        prfSecret prims.core pkSeed skSeed a := by
    intro pkSeed skSeed a ha
    rw [oracleSecret_natural prims.core F e pkSeed skSeed a]
    change (pure (prims.Thash pkSeed (prims.adrsToKey a) [e skSeed]) : ProbComp prims.Y) = _
    rw [hprf pkSeed skSeed a ha]
    rfl
  apply SignatureAlg.ext
  · change F.toMonadHom (liftM pkSeedDist >>= romKeygenAt prims.core e) = _
    rw [F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun pkSeed => ?_
    rw [romKeygenAt, F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun skSeed => ?_
    rw [F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun skPrf => ?_
    rw [F.toMonadHom.mmap_bind, GeneralScheme.keygenInternalWithSecretM_natural prims.core F _ _
      (hSecret pkSeed skSeed), GeneralScheme.keygenInternalWithSecretM_prfSecret,
      ← GeneralHypertree.rootM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree, pure_bind, F.toMonadHom.mmap_pure]
    congr 1
    exact Prod.ext (GeneralScheme.keygenInternal_fst vp prims skSeed skPrf pkSeed).symm
      (GeneralScheme.keygenInternal_snd vp prims skSeed skPrf pkSeed).symm
  · funext pk sk msg
    change F.toMonadHom ((romScheme prims.core e optRand pkSeedDist).sign pk sk msg) = _
    rw [romScheme_sign, F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun addrnd => ?_
    have hR : F.toMonadHom (query (spec := prfMsgSpec prims.core) ⟨sk.skPrf, addrnd, msg⟩ :
        OracleComp (unifSpec + hashSpec prims.core) prims.Y) =
          pure (prims.PRFmsg sk.skPrf addrnd msg) := by
      simp [F, unifFwdAnswerImpl, romAnswer]
      rfl
    rw [F.toMonadHom.mmap_bind, hR, pure_bind,
      GeneralScheme.signInternalWithSecretRandomizerM_natural prims.core F _ _
        (hSecret sk.pkSeed sk.skSeed),
      GeneralScheme.signInternalWithSecretRandomizerM_prfSecret,
      ← GeneralScheme.signInternalM_eq_signInternalWithRandomizerM,
      ← GeneralScheme.signInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree]
    rfl
  · funext pk msg sig
    change F.toMonadHom (GeneralScheme.verifyInternalM vp prims.core msg sig pk) = _
    rw [GeneralScheme.verifyInternalM_natural vp prims.core F,
      ← GeneralScheme.verifyInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree]
    rfl

end Conformance

end SLHDSA.Security
