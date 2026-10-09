/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteConformance

/-!
# SLH-DSA over a single SHAKE256 oracle, checked

`HashSig.SLHDSA.Security.ByteModel` states SLH-DSA over one random oracle on byte strings, and
`HashSig.SLHDSA.Security.ByteConformance` identifies it, with the oracle answered by SHAKE256,
with FIPS 205's SHAKE internal algorithms. This file checks both at concrete parameter sets.

* **Conformance at the shipped sets, both signing modes.** At SLH-DSA-SHAKE-128s with
  deterministic signing (`opt_rand = PK.seed`) and at SLH-DSA-SHAKE-256f with hedged signing
  (`opt_rand` uniform), the single-oracle scheme answered by SHAKE256 is `internalAlg` at the
  SHAKE bundle; key generation, signing and verification are restated one by one.
* **The per-role equations evaluate**, in the `slhdsa_byte_model_tests` executable. At 128s the
  `n`-byte prefix of the SHAKE256 answer at the tweakable-hash and `PRF_msg` layouts, and the
  whole answer at the `H_msg` layout, equal the landed `shakeThash`, `shakePRFmsg` and
  `shakeHmsg` on concrete inputs; the same answer at a layout with `PK.seed` and `ADRS` swapped
  does not (negative control). Prefix consistency evaluates at the 256s widths `n = 32`, `m = 47`.
* **The oracle does not separate roles.** A tweakable-hash string and a `PRF_msg` string can be the
  same bytes, so the two queries are one oracle point (`encode_thash_eq_encode_prfMsg`): the model
  is a single function, as FIPS 205's SHAKE instantiation is, unlike the three-oracle model of
  `HashSig.SLHDSA.Security.Target`.
* **Layout shapes**: the `F`, `H_msg` and `PRF_msg` strings at 128s have `64`, `48 + |M|` and
  `32 + |M|` bytes; zero padding of `bytesOfList`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.ByteModelTest

open Concrete Security

/-- SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-- SLH-DSA-SHAKE-256f. -/
abbrev vp256f : ValidatedParams := FipsParameterSet.validatedParams .SLHDSA_SHAKE_256f

/-- Deterministic signing (FIPS 205 Algorithm 19 line 2): `opt_rand = PK.seed`. -/
def deterministicRandomizer (vp : ValidatedParams) :
    PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y :=
  fun pk => pure (shakeRandomizerOfPkSeed vp.params pk.pkSeed)

/-- Hedged signing: `opt_rand` uniform. -/
noncomputable def hedgedRandomizer (vp : ValidatedParams) :
    PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y :=
  fun _ => $ᵗ (shakeCore vp).Y

/-! ## Conformance at the shipped sets -/

/-- Deterministic SLH-DSA-SHAKE-128s over the single oracle, answered by SHAKE256, is FIPS 205. -/
example :
    (shakeRomScheme vp128s (deterministicRandomizer vp128s) ($ᵗ (shakeCore vp128s).PkSeed)).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp128s))) =
      internalAlg vp128s (shakePrimitives vp128s.params) (deterministicRandomizer vp128s)
        ($ᵗ (shakeCore vp128s).PkSeed) :=
  shakeRomScheme_map_shakeAnswer_validatedParams .SLHDSA_SHAKE_128s _ _

/-- Hedged SLH-DSA-SHAKE-256f over the single oracle, answered by SHAKE256, is FIPS 205. -/
example :
    (shakeRomScheme vp256f (hedgedRandomizer vp256f) ($ᵗ (shakeCore vp256f).PkSeed)).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp256f))) =
      internalAlg vp256f (shakePrimitives vp256f.params) (hedgedRandomizer vp256f)
        ($ᵗ (shakeCore vp256f).PkSeed) :=
  shakeRomScheme_map_shakeAnswer_validatedParams .SLHDSA_SHAKE_256f _ _

section Components

variable (pkSeedDist : ProbComp (shakeCore vp128s).PkSeed)

private theorem conformance128s :
    (shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp128s))) =
      internalAlg vp128s (shakePrimitives vp128s.params) (deterministicRandomizer vp128s)
        pkSeedDist :=
  shakeRomScheme_map_shakeAnswer_validatedParams .SLHDSA_SHAKE_128s _ _

/-- Key generation answered by SHAKE256 is `slh_keygen_internal` at freshly drawn seeds. -/
example :
    simulateQ (unifFwdAnswerImpl (shakeAnswer vp128s))
        (shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).keygen =
      (do
        let pkSeed ← pkSeedDist
        let skSeed ← $ᵗ (shakePrimitives vp128s.params).SkSeed
        let skPrf ← $ᵗ (shakePrimitives vp128s.params).SkPrf
        pure (GeneralScheme.keygenInternal vp128s (shakePrimitives vp128s.params) skSeed skPrf
          pkSeed)) :=
  congrArg SignatureAlg.keygen (conformance128s pkSeedDist)

/-- Deterministic signing answered by SHAKE256 is `slh_sign_internal` at `opt_rand = PK.seed`. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (sk : SecretKeyCore (shakeCore vp128s))
    (msg : List Byte) :
    simulateQ (unifFwdAnswerImpl (shakeAnswer vp128s))
        ((shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).sign pk sk msg) =
      pure (GeneralScheme.signInternal vp128s (shakePrimitives vp128s.params) msg sk
        pk.pkSeed) := by
  refine (congrArg (fun A => A.sign pk sk msg) (conformance128s pkSeedDist)).trans ?_
  simp only [internalAlg, deterministicRandomizer, shakeRandomizerOfPkSeed, id]
  rfl

/-- Verification answered by SHAKE256 is `slh_verify_internal`. -/
example (pk : PublicKeyCore (shakeCore vp128s)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp128s (shakeCore vp128s)) :
    simulateQ (unifFwdAnswerImpl (shakeAnswer vp128s))
        ((shakeRomScheme vp128s (deterministicRandomizer vp128s) pkSeedDist).verify pk msg sig) =
      pure (GeneralScheme.verifyInternal vp128s (shakePrimitives vp128s.params) msg sig pk) :=
  congrArg (fun A => A.verify pk msg sig) (conformance128s pkSeedDist)

end Components

/-! ## The per-role equations, evaluated -/

/-- A fixed 16-byte value. -/
def seed16 : Bytes 16 := Vector.ofFn fun i => (i.val * 7 + 3).toUInt8

/-- A second fixed 16-byte value. -/
def node16 : Bytes 16 := Vector.ofFn fun i => (i.val * 13 + 1).toUInt8

/-- A WOTS+ hash address. -/
def adrs : Adrs := ((Adrs.zero.setLayerAddress 2).setTreeAddress 5).setTypeAndClear .wotsHash

def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"byte-model check failed: {label}")

/-- The SHAKE256 answer at each layout, read at the role's width, against the landed SHAKE
function of that role, with a layout-order negative control and prefix consistency. -/
def checkRoles : IO Unit := do
  ensure "F at 128s is shakeThash"
    (prefixBytes 16 (shakeAnswer vp128s (encode vp128s (.inl (.thash seed16 adrs.toVector
      [node16])))) == shakeThash vp128s.params seed16 adrs.toVector [node16])
  ensure "H_msg at 128s is shakeHmsg"
    (shakeHmsg vp128s.params node16 seed16 node16 [1, 2, 3] ==
      shakeAnswer vp128s (encode vp128s (.inl (.hmsg node16 seed16 node16 [1, 2, 3]))))
  ensure "PRF_msg at 128s is shakePRFmsg"
    (prefixBytes 16 (shakeAnswer vp128s (encode vp128s (.inr ⟨node16, seed16, [9, 8]⟩))) ==
      shakePRFmsg node16 seed16 [9, 8])
  ensure "ADRS before PK.seed is not F"
    (prefixBytes 16 (shakeAnswer vp128s (adrs.toBytes ++ seed16.toList ++ node16.toList)) !=
      shakeThash vp128s.params seed16 adrs.toVector [node16])
  ensure "PRF is the tweakable hash at the PRF address"
    (shakeThash vp128s.params seed16 (adrs.setTypeAndClear .wotsPrf).toVector [node16] ==
      shakePRF seed16 node16 (adrs.setTypeAndClear .wotsPrf))
  ensure "SHAKE256 prefix consistency at n = 32, m = 47"
    ((Keccak.shake256 (seed16.toList ++ adrs.toBytes).toByteArray 47).data.toList.take 32 ==
      (Keccak.shake256 (seed16.toList ++ adrs.toBytes).toByteArray 32).data.toList)
  ensure "zero padding" (bytesOfList 4 [1, 2] == #v[1, 2, 0, 0])
  ensure "truncation" (bytesOfList 2 [1, 2, 3] == #v[1, 2])

/-! ## The oracle does not separate roles -/

/-- At 128s, every tweakable-hash string `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` is also the `PRF_msg`
string with `SK.prf = PK.seed`, `opt_rand` the first half of `ADRS` and the message the rest. -/
theorem encode_thash_eq_encode_prfMsg (pkSeed : Bytes vp128s.params.n) (adrsKey : Bytes 32)
    (xs : List (Bytes vp128s.params.n)) :
    encode vp128s (.inl (.thash pkSeed adrsKey xs)) =
      encode vp128s (.inr ⟨pkSeed, bytesOfList vp128s.params.n adrsKey.toList,
        adrsKey.toList.drop vp128s.params.n ++ (xs.map Vector.toList).flatten⟩) := by
  refine (encode_thash vp128s pkSeed adrsKey xs).trans ?_
  change _ = pkSeed.toList ++ (bytesOfList vp128s.params.n adrsKey.toList).toList ++
    (adrsKey.toList.drop vp128s.params.n ++ (xs.map Vector.toList).flatten)
  rw [toList_bytesOfList_of_le (by rw [Vector.length_toList]; decide), List.append_assoc,
    List.append_assoc, ← List.append_assoc (List.take _ _), List.take_append_drop]

/-! ## Layout shapes -/

example : (encode vp128s (.inl (.thash seed16 adrs.toVector [node16]))).length = 64 :=
  (length_encode_thash vp128s seed16 adrs.toVector [node16]).trans rfl

example (msg : List Byte) :
    (encode vp128s (.inl (.hmsg node16 seed16 node16 msg))).length = 48 + msg.length :=
  (length_encode_hmsg vp128s seed16 node16 node16 msg).trans rfl

example (msg : List Byte) :
    (encode vp128s (.inr ⟨node16, seed16, msg⟩)).length = 32 + msg.length :=
  (length_encode_prfMsg vp128s ⟨node16, seed16, msg⟩).trans rfl

example : ∀ set ∈ FipsParameterSet.all,
    set.validatedParams.params.n ≤ set.validatedParams.params.m ∧
      set.validatedParams.params.m < 136 :=
  fun set _ => ⟨set.n_le_m, set.m_lt_136⟩

def main : IO Unit := do
  checkRoles
  IO.println "SLH-DSA byte-model tests: PASS \
    (SHAKE256 at the F, H_msg and PRF_msg layouts, PRF, prefix consistency)"

end SLHDSA.ByteModelTest

def main : IO Unit := SLHDSA.ByteModelTest.main
