/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteModel
public import HashSig.SLHDSA.Security.RomConformance

/-!
# The single-oracle scheme at SHAKE256 is FIPS 205

`shakeRomScheme vp` of `HashSig.SLHDSA.Security.ByteModel` is SLH-DSA over a random oracle on byte
strings with `m`-byte answers. Answering that oracle by SHAKE256 itself, `shakeAnswer vp x`, the
`m`-byte output of `shake256` on `x`, gives FIPS 205's SHAKE internal algorithms: key generation,
signing and verification are `GeneralScheme.keygenInternal`, `signInternal` and `verifyInternal`
at the SHAKE bundle `shakePrimitives` of `HashSig.SLHDSA.Concrete.FIPS`. The identification needs
`n ≤ m < 136`: every role reads a prefix of one `m`-byte answer, and SHAKE256's outputs of length
below its `136`-byte rate are prefixes of one another. Every FIPS 205 parameter set satisfies it.

## Main statements

* `Keccak.shake256_data_toList_take`: below the rate, the `n`-byte SHAKE256 output is the first
  `n` bytes of the `m`-byte one.
* `prefixBytes_shakeAnswer_encode_thash`, `shakeAnswer_encode_hmsg`,
  `prefixBytes_shakeAnswer_encode_prfMsg`: the oracle at each FIPS 205 §11.1 layout is the landed
  SHAKE function of that role, `shakeThash`, `shakeHmsg` and `shakePRFmsg`.
* `shakeThash_toVector_singleton`: the tweakable hash at a `PRF` address applied to `SK.seed` is
  `shakePRF`.
* `unifFwdAnswerImpl_shakeAnswer_compose_encImpl`: answering each typed query by SHAKE256 at its
  encoding is answering it by the SHAKE bundle.
* `romScheme_shakeCore_map_romAnswer`: the three-oracle scheme answered by the SHAKE bundle is
  `internalAlg vp (shakePrimitives vp.params)`.
* `shakeRomScheme_map_shakeAnswer`: **conformance** — `shakeRomScheme vp optRand pkSeedDist` with
  its oracle answered by `shakeAnswer vp` is `internalAlg vp (shakePrimitives vp.params) optRand
  pkSeedDist`, for every `opt_rand` source, deterministic and hedged signing included, and every
  public-seed distribution.
* `shakeRomScheme_map_shakeAnswer_validatedParams`: the same at every FIPS 205 parameter set,
  without side conditions.

## References

* NIST FIPS 205, §9 (Algorithms 18–20), §11.1 (SLH-DSA using SHAKE).
* NIST FIPS 202, §4 (the sponge construction) and §6.2 (SHAKE256).
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Concrete

/-! ## Byte-array bridges -/

private theorem byteArray_toList_loop (bs : ByteArray) (i : ℕ) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
      rw [ih]
      have hi : i < bs.data.size := by rwa [ByteArray.size_data]
      have hi' : i < bs.data.toList.length := by simpa using hi
      simp [ByteArray.get!, List.drop_eq_getElem_cons hi', getElem!_pos bs.data i hi]
  | case2 i r h =>
      have hi : bs.data.toList.length ≤ i := by
        simp only [Array.length_toList]
        rw [ByteArray.size_data]
        omega
      simp [List.drop_eq_nil_of_le hi]

/-- `ByteArray.toList` lists the bytes of the underlying array. -/
theorem byteArray_toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  simp [ByteArray.toList, byteArray_toList_loop]

/-- A byte array is the packing of its byte list. -/
theorem toByteArray_eq_of_data_toList_eq {l : List Byte} {bs : ByteArray}
    (h : bs.data.toList = l) : l.toByteArray = bs := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray, h]

/-- A fixed-width vector packed as a byte array keeps its bytes. -/
@[simp] theorem data_toList_bytesToByteArray {n : ℕ} (v : Bytes n) :
    (bytesToByteArray v).data.toList = v.toList := rfl

private theorem data_toList_foldl_bytesToByteArray {n : ℕ} (xs : List (Bytes n))
    (acc : ByteArray) :
    (xs.foldl (fun out value => out ++ bytesToByteArray value) acc).data.toList =
      acc.data.toList ++ (xs.map Vector.toList).flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, ByteArray.data_append]

/-- `concatBytes` concatenates the bytes of its nodes in order. -/
@[simp] theorem data_toList_concatBytes {n : ℕ} (xs : List (Bytes n)) :
    (concatBytes xs).data.toList = (xs.map Vector.toList).flatten := by
  rw [concatBytes, data_toList_foldl_bytesToByteArray]
  rfl

/-- Reading the first `k` bytes of a byte array of at least `k` bytes. -/
theorem toList_byteArrayPrefixOrZero_of_le {bs : ByteArray} {k : ℕ} (h : k ≤ bs.size) :
    (byteArrayPrefixOrZero bs k).toList = bs.data.toList.take k := by
  have hraw : (bs.extract 0 k).toList = bs.data.toList.take k := by
    rw [byteArray_toList_eq_data_toList, ByteArray.data_extract, Array.toList_extract]
    simp
  have hlen : (bs.extract 0 k).toList.length = k := by
    rw [hraw, List.length_take, Array.length_toList, ByteArray.size_data]
    omega
  unfold byteArrayPrefixOrZero byteArrayPrefixChecked
  simp only [decodeExact, hlen, ↓reduceDIte]
  simpa using hraw

namespace Keccak

/-- One squeezed block, as a byte list. -/
theorem squeeze_data_toList (s : Array UInt64) (k : ℕ) :
    (squeeze s k).data.toList = List.ofFn fun i : Fin k =>
      ((s[i.val / 8]! >>> ((i.val % 8) * 8).toUInt64) &&& 0xFF).toUInt8 := by
  simp [squeeze]

/-- Below the rate the XOF squeeze is a single block squeeze. -/
theorem squeezeXof_data_toList_of_lt (s : Array UInt64) {k : ℕ} (hk : k < 136) :
    (squeezeXof s 136 k).data.toList = (squeeze s k).data.toList := by
  simp [squeezeXof, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, squeezeFullBlocks]

/-- **Prefix consistency of SHAKE256 below the rate**: for `n ≤ m < 136`, the `n`-byte output is
the first `n` bytes of the `m`-byte output. -/
theorem shake256_data_toList_take {x : ByteArray} {n m : ℕ} (hnm : n ≤ m) (hm : m < 136) :
    (shake256 x m).data.toList.take n = (shake256 x n).data.toList := by
  simp only [shake256]
  rw [squeezeXof_data_toList_of_lt _ hm, squeezeXof_data_toList_of_lt _ (lt_of_le_of_lt hnm hm),
    squeeze_data_toList, squeeze_data_toList]
  apply List.ext_getElem
  · simp [hnm]
  · intro i h₁ h₂
    simp

end Keccak

/-- A fixed-width read of a SHAKE256 output of exactly that width is the whole output. -/
theorem toList_byteArrayPrefixOrZero_shake256 (x : ByteArray) (k : ℕ) :
    (byteArrayPrefixOrZero (Keccak.shake256 x k) k).toList = (Keccak.shake256 x k).data.toList := by
  rw [toList_byteArrayPrefixOrZero_of_le (by simp), List.take_of_length_le]
  simp

/-- The tweakable hash at a `PRF` address applied to the secret seed is `PRF`: FIPS 205 lays out
both as `PK.seed ‖ ADRS ‖ SK.seed`. -/
theorem shakeThash_toVector_singleton (p : Params) (pkSeed skSeed : Bytes p.n) (a : Adrs) :
    shakeThash p pkSeed a.toVector [skSeed] = shakePRF pkSeed skSeed a := by
  have : bytesToByteArray pkSeed ++ shakeAddressKey a.toVector ++ concatBytes [skSeed] =
      bytesToByteArray pkSeed ++ shakeAddress a ++ bytesToByteArray skSeed := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [ByteArray.data_append, shakeAddressKey, shakeAddress, Adrs.toVector]
  simp only [shakeThash, shakePRF, this]

end SLHDSA.Concrete

namespace SLHDSA.FipsParameterSet

/-- Every FIPS 205 parameter set has its node width at most its digest width. -/
theorem n_le_m (set : FipsParameterSet) :
    set.validatedParams.params.n ≤ set.validatedParams.params.m := by
  cases set <;> decide

/-- Every FIPS 205 parameter set has its digest width below the SHAKE256 rate of `136` bytes. -/
theorem m_lt_136 (set : FipsParameterSet) :
    set.validatedParams.params.m < 136 := by
  cases set <;> decide

end SLHDSA.FipsParameterSet

namespace SLHDSA.Security

open Concrete

variable (vp : ValidatedParams)

/-- **SHAKE256 as the byte-string oracle**: the answer at `x` is the `m`-byte output
`SHAKE256(x, 8m)`. -/
@[expose] def shakeAnswer : QueryImpl (shakeSpec vp) Id := fun x =>
  byteArrayPrefixOrZero (Keccak.shake256 x.toByteArray vp.params.m) vp.params.m

variable {vp}

/-- The SHAKE256 answer lists the bytes of the `m`-byte output. -/
theorem toList_shakeAnswer (x : List Byte) :
    (shakeAnswer vp x).toList = (Keccak.shake256 x.toByteArray vp.params.m).data.toList :=
  toList_byteArrayPrefixOrZero_shake256 _ _

/-- For `n ≤ m < 136`, the first `n` bytes of the SHAKE256 answer are the `n`-byte output. -/
theorem toList_prefixBytes_shakeAnswer (hnm : vp.params.n ≤ vp.params.m)
    (hm : vp.params.m < 136) (x : List Byte) :
    (prefixBytes vp.params.n (shakeAnswer vp x)).toList =
      (Keccak.shake256 x.toByteArray vp.params.n).data.toList := by
  rw [toList_prefixBytes_of_le hnm, toList_shakeAnswer, Keccak.shake256_data_toList_take hnm hm]

/-! ## The oracle at each layout -/

/-- The oracle at the tweakable-hash layout, read at `n` bytes, is FIPS 205's SHAKE `T_ℓ`. -/
theorem prefixBytes_shakeAnswer_encode_thash (hnm : vp.params.n ≤ vp.params.m)
    (hm : vp.params.m < 136) (pkSeed : Bytes vp.params.n) (adrsKey : Bytes 32)
    (xs : List (Bytes vp.params.n)) :
    prefixBytes vp.params.n (shakeAnswer vp (encode vp (.inl (.thash pkSeed adrsKey xs)))) =
      shakeThash vp.params pkSeed adrsKey xs := by
  apply Vector.toList_inj.mp
  rw [toList_prefixBytes_shakeAnswer hnm hm, shakeThash, toList_byteArrayPrefixOrZero_shake256,
    toByteArray_eq_of_data_toList_eq (l := encode vp _)]
  simp [ByteArray.data_append, shakeAddressKey]

/-- The oracle at the `H_msg` layout is FIPS 205's SHAKE `H_msg`. -/
theorem shakeAnswer_encode_hmsg (r pkSeed pkRoot : Bytes vp.params.n) (msg : List Byte) :
    shakeAnswer vp (encode vp (.inl (.hmsg r pkSeed pkRoot msg))) =
      shakeHmsg vp.params r pkSeed pkRoot msg := by
  rw [shakeAnswer, shakeHmsg, toByteArray_eq_of_data_toList_eq (l := encode vp _)]
  simp [ByteArray.data_append]

private theorem prefixBytes_shakeAnswer_append (hnm : vp.params.n ≤ vp.params.m)
    (hm : vp.params.m < 136) (skPrf optRand : Bytes vp.params.n) (msg : List Byte) :
    prefixBytes vp.params.n (shakeAnswer vp (skPrf.toList ++ optRand.toList ++ msg)) =
      shakePRFmsg skPrf optRand msg := by
  apply Vector.toList_inj.mp
  rw [toList_prefixBytes_shakeAnswer hnm hm, shakePRFmsg, toList_byteArrayPrefixOrZero_shake256,
    toByteArray_eq_of_data_toList_eq (l := skPrf.toList ++ optRand.toList ++ msg)]
  simp [ByteArray.data_append]

/-- The oracle at the `PRF_msg` layout, read at `n` bytes, is FIPS 205's SHAKE `PRF_msg`. -/
theorem prefixBytes_shakeAnswer_encode_prfMsg (hnm : vp.params.n ≤ vp.params.m)
    (hm : vp.params.m < 136) (q : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y) :
    prefixBytes vp.params.n (shakeAnswer vp (encode vp (.inr q))) =
      shakePRFmsg (n := vp.params.n) q.skPrf q.optRand q.msg :=
  prefixBytes_shakeAnswer_append hnm hm q.skPrf q.optRand q.msg

/-! ## Scheme conformance -/

/-- **The three-oracle scheme at the SHAKE bundle is FIPS 205**: answering the tweakable hash,
`H_msg` and `PRF_msg` of `romScheme` by the landed SHAKE functions gives FIPS 205's SHAKE internal
algorithms. -/
theorem romScheme_shakeCore_map_romAnswer
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) :
    (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer (shakePrimitives vp.params)))) =
      internalAlg vp (shakePrimitives vp.params) optRand pkSeedDist :=
  romScheme_map_romAnswer (shakePrimitives vp.params) (Equiv.refl _)
    (fun pkSeed skSeed a _ => shakeThash_toVector_singleton vp.params pkSeed skSeed a)
    optRand pkSeedDist

/-- **Per-query conformance**: for `n ≤ m < 136`, answering each typed query by the SHAKE256 oracle
at its encoding is answering it by the landed SHAKE function of its role. -/
theorem unifFwdAnswerImpl_shakeAnswer_compose_encImpl (hnm : vp.params.n ≤ vp.params.m)
    (hm : vp.params.m < 136) :
    unifFwdAnswerImpl (shakeAnswer vp) ∘ₛ encImpl vp =
      unifFwdAnswerImpl (romAnswer (shakePrimitives vp.params)) := by
  funext t
  rcases t with n | (q | q)
  · simp [encImpl, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_query_left]
  · cases q with
    | thash pkSeed adrsKey xs =>
        simp only [QueryImpl.apply_compose, encImpl, encHashImpl, unifFwdAnswerImpl,
          QueryImpl.add_apply_inr]
        change prefixBytes vp.params.n <$> (pure _ : ProbComp _) = (pure _ : ProbComp _)
        rw [map_pure]
        exact congrArg pure (prefixBytes_shakeAnswer_encode_thash hnm hm pkSeed adrsKey xs)
    | hmsg r pkSeed pkRoot msg =>
        simp only [QueryImpl.apply_compose, encImpl, encHashImpl, unifFwdAnswerImpl,
          QueryImpl.add_apply_inr]
        change (pure _ : ProbComp _) = (pure _ : ProbComp _)
        exact congrArg pure (shakeAnswer_encode_hmsg r pkSeed pkRoot msg)
  · simp only [QueryImpl.apply_compose, encImpl, encHashImpl, unifFwdAnswerImpl,
      QueryImpl.add_apply_inr]
    change prefixBytes vp.params.n <$> (pure _ : ProbComp _) = (pure _ : ProbComp _)
    rw [map_pure]
    exact congrArg pure (prefixBytes_shakeAnswer_encode_prfMsg hnm hm q)

/-- **Conformance of the single-oracle scheme.** For `n ≤ m < 136`, SLH-DSA over one random oracle
on byte strings, with that oracle answered by SHAKE256 (`shakeAnswer vp`) and its uniform draws
kept, is FIPS 205's SHAKE internal key generation, signing and verification
(`internalAlg vp (shakePrimitives vp.params)`), for every `opt_rand` source and every public-seed
distribution. -/
theorem shakeRomScheme_map_shakeAnswer (hnm : vp.params.n ≤ vp.params.m)
    (hm : vp.params.m < 136)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed) :
    (shakeRomScheme vp optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (shakeAnswer vp))) =
      internalAlg vp (shakePrimitives vp.params) optRand pkSeedDist := by
  rw [← romScheme_shakeCore_map_romAnswer,
    ← unifFwdAnswerImpl_shakeAnswer_compose_encImpl hnm hm]
  apply SignatureAlg.ext
  · simp [shakeRomScheme]
  · funext pk sk msg
    simp [shakeRomScheme]
  · funext pk msg sig
    simp [shakeRomScheme]

/-- **Conformance at the FIPS 205 parameter sets.** At every approved parameter set, SLH-DSA over
one random oracle on byte strings, with that oracle answered by SHAKE256, is FIPS 205's SHAKE
internal key generation, signing and verification. -/
theorem shakeRomScheme_map_shakeAnswer_validatedParams (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeedDist : ProbComp (shakeCore set.validatedParams).PkSeed) :
    (shakeRomScheme set.validatedParams optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (shakeAnswer set.validatedParams))) =
      internalAlg set.validatedParams (shakePrimitives set.validatedParams.params) optRand
        pkSeedDist :=
  shakeRomScheme_map_shakeAnswer set.n_le_m set.m_lt_136 optRand pkSeedDist

end SLHDSA.Security
