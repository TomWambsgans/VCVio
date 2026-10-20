/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProjectedHazards
import HashSig.SLHDSA.Security.AddressKeys
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The virtual hit and the honest input at a linked point, charged

At `n = 32`, `HashSig.SLHDSA.Security.ByteLinkedBound` bounds the advantage against SLH-DSA over
one SHAKE256 oracle, at a public seed, by the events of the verifying run plus the cost `κ` of a
further charge (`DeferredCharge`) to which the virtual hit (`VirtualHit`) and the honest input at a
linked point (`LinkedHonestInput`) are charged. This module supplies that charge,
`linkedCharge`, at every public seed, with `κ = (qs + 1) / |Y|`. It is a classical
random-oracle statement; nothing here is quantum.

## The charge

* **The virtual hit is a projected hit** (`projHazard_of_virtualHit_fill`). The honest entry of a
  virtual hit is the point of a node `κ` at its drawn children, so its cached value is the label
  of `κ`, and the linked point at its key reads the `H_msg` point `H_msg(PK.seed, PK.seed, ·, ·)`,
  whose first `n` bytes are that label. The projected keys of the linked points
  (`linkedProjKeys`) read such an `H_msg` answer, through its first `n` bytes, at the node at the
  key with the bytes of `PK.seed`; the first `n` bytes of a uniform answer are uniform
  (`prEvent_uniformSample_prefixBytes_eq_le`). So each `H_msg` entry at that key is charged
  `1 / |Y|` once, on whichever side of the label's draw it falls
  (`CanonicalGraph.ProjKeys.isCharged`).
* **The honest input at a linked point is a root event** (`rootCharge`). In every deferred run of
  the lab experiment the cell of the top-layer root holds `PK.root`
  (`cell_rootNode_of_mem_support_deferredImpl_labExperiment`), and a linked point has `PK.root`
  as its first input. If the key with the bytes of `PK.seed` is the key of a node `κ₀`, an honest
  entry at a linked point is the point of `κ₀`, so the first child cell of `κ₀` holds the value of
  the root cell (`pairHazard_of_linkedHonestInput_fill`); the root is no node's child
  (`inr_rootNode_not_mem_ch`), so the two cells are distinct and are drawn equal with probability
  `1 / |Y|` (`CanonicalGraph.isCharged_pairHazard`). A node with no children has no honest entry
  at a linked point, so that case does not fire. Otherwise the honest input is a secret queried
  at a linked point, so the first secret seed is the value of the root cell
  (`rootSeed_of_linkedHonestInput_fill`), a hazard of the seed draw of probability `1 / |Y|`.
  Under key separation a secret never sits at a node's key, so exactly one case is charged per
  public seed.

## The budget

Every projected entry is a cached `H_msg` point. With `A` the public entries at node keys, `B`
the cached derivable public points and `H` the cached `H_msg` points of a lab run of an adversary
with budget `(qh, qs)`, `A + B ≤ qh + V` and `A + B + H ≤ qh + qs + V`. So the joint budget with the
linked charge is at most `(2 (qh + V) + 2 qs + 2) / |Y|` with the charge of the message-`PRF` key
(`withinBudget_linkedCharge_of_romQueryBound`) and `(2 (qh + V) + qs + 2) / |Y|` with the
fixed-key charge (`withinBudget_linkedCharge_of_romQueryBound_hedged`). At the verifying
adversary, of budget `(qh + V, qs)`, each exceeds the landed joint budget by `(qs + 1) / |Y|`.

## Main statements

- `shakeAdvantage_pure_le_securityBound_add_of_n_eq_32`: at `n = 32`, at every public seed and
  every `opt_rand` distribution, the advantage is at most
  `securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + (qs + 1) / |Y|`.
- `shakeAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged`: with `opt_rand pk = PK.seed` with
  probability at most `ε`, at most
  `securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y| +
  (qs + 1) / |Y|`.

Neither needs the public seed to avoid the keys of honest addresses.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

/-! ## The first `n` bytes of a uniform answer -/

/-- Splitting `m` bytes into the first `n` and the rest is a bijection. -/
theorem bijective_prefixBytes_drop {n m : ℕ} (hnm : n ≤ m) :
    Function.Bijective (fun u : Bytes m ↦
      (prefixBytes n u, bytesOfList (m - n) (u.toList.drop n))) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun ab ↦
    bytesOfList m (ab.1.toList ++ ab.2.toList), fun u ↦ ?_, fun ⟨a, b⟩ ↦ ?_⟩
  · have hl : (u.toList.drop n).length = m - n := by simp
    have h1 : (prefixBytes n u).toList ++ (bytesOfList (m - n) (u.toList.drop n)).toList =
        u.toList := by
      rw [toList_prefixBytes_of_le hnm, toList_bytesOfList_of_le hl.ge,
        List.take_of_length_le hl.le, List.take_append_drop]
    simp only [h1, bytesOfList_toList]
  · have hl : (a.toList ++ b.toList).length = m := by simp; omega
    have h1 : (bytesOfList m (a.toList ++ b.toList)).toList = a.toList ++ b.toList := by
      rw [toList_bytesOfList_of_le hl.ge, List.take_of_length_le hl.le]
    refine Prod.ext ?_ ?_
    · simp only [prefixBytes, h1]
      rw [bytesOfList_append_of_length_eq (by simp), bytesOfList_toList]
    · simp only [h1]
      rw [List.drop_left' (by simp), bytesOfList_toList]

/-- The first `n` bytes of a uniform `m`-byte vector take any value with probability at most
`1 / |Bytes n|`. -/
theorem prEvent_uniformSample_prefixBytes_eq_le {n m : ℕ} (hnm : n ≤ m) (ℓ : Bytes n) :
    Pr{let u ← $ᵗ (Bytes m)}[prefixBytes n u = ℓ] ≤ (Nat.card (Bytes n) : ℝ≥0∞)⁻¹ :=
  calc Pr{let u ← $ᵗ (Bytes m)}[prefixBytes n u = ℓ]
      = Pr{let y ← $ᵗ (Bytes n × Bytes (m - n))}[y.1 = ℓ] :=
        SampleableType.prEvent_uniformSample_comp_of_bijective (bijective_prefixBytes_drop hnm)
          (fun y ↦ y.1 = ℓ)
    _ = Pr{let x ← $ᵗ (Bytes n)}[x = ℓ] := SampleableType.prEvent_uniformSample_fst (· = ℓ)
    _ ≤ _ := (SampleableType.prEvent_uniformSample_eq_singleton_natCard ℓ).le

/-! ## The root cell -/

section Root

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

variable (vp) in
/-- The address of the top-layer root, node `(h', 0)` of the XMSS tree at layer `d - 1`. -/
abbrev rootAdrs : Adrs :=
  xmssNodeAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) vp.params.hp 0

/-- The top-layer root is an address of the union ledger. -/
theorem rootAdrs_mem_constructionAddresses : rootAdrs vp ∈ constructionAddresses vp := by
  rw [rootAdrs, ← LayerTreeCoord.top_toAdrs_layerAdrs]
  exact xmssNodeAdrs_mem_constructionAddresses _ vp.valid.hp_pos le_rfl (by simp)

/-- The node of the top-layer root. -/
def rootNode : NodeKey core :=
  ⟨core.adrsToKey (rootAdrs vp), rootAdrs vp, rootAdrs_mem_constructionAddresses, rfl⟩

omit core in
/-- The top-layer root is no node child of an address of the union ledger: the node children of a
ledger address are `WOTS_HASH`, `WOTS_PK` or `FORS_TREE` addresses, or XMSS nodes below height
`h'`. -/
theorem inr_rootAdrs_not_mem_childAdrs {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    .inr (rootAdrs vp) ∉ childAdrs vp a := by
  intro hb
  have hroot : rootAdrs vp = ⟨vp.params.d - 1, 0, 2, 0, vp.params.hp, 0⟩ := rfl
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
    simp [childAdrs_forsNodeAdrs_zero] at hb
  · obtain ⟨⟨⟨pos, tree⟩, z, j⟩, hmem, rfl⟩ := List.mem_map.1 h
    rw [childAdrs_forsNodeAdrs vp (mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2).1]
      at hb
    simp [hroot, forsNodeAdrs_eq] at hb
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
    simp [childAdrs_forsPkAdrs, hroot, forsNodeAdrs_eq] at hb
  · obtain ⟨⟨_, ⟨t, _⟩⟩, -, rfl⟩ := List.mem_map.1 h
    simp only [wotsStepAdrs] at hb
    rcases t with _ | t
    · simp [childAdrs_wotsChainAdrs_setHashAddress_zero] at hb
    · rw [childAdrs_wotsChainAdrs_setHashAddress_succ] at hb
      simp [hroot, wotsChainAdrs_setHashAddress_eq] at hb
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
    simp [childAdrs_wotsPkAdrs, hroot, wotsChainAdrs_setHashAddress_eq] at hb
  · obtain ⟨⟨_, z, j⟩, hmem, rfl⟩ := List.mem_map.1 h
    obtain ⟨hz, hzh, -⟩ := mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2
    rcases (by omega : z = 1 ∨ 1 < z) with rfl | hz1
    · simp [childAdrs_xmssNodeAdrs_one, hroot, wotsPkAdrs_eq] at hb
    · rw [childAdrs_xmssNodeAdrs vp hz1] at hb
      simp only [hroot, xmssNodeAdrs_eq, List.mem_cons, Sum.inr.injEq, Adrs.mk.injEq,
        List.not_mem_nil, or_false] at hb
      omega

variable {core}

/-- **The root is no node's child**, under the key discipline. -/
theorem inr_rootNode_not_mem_ch (hd : core.KeyDiscipline vp) (pkSeed : core.PkSeed)
    (κ : NodeKey core) :
    (.inr (rootNode core) : DeriveQuery core ⊕ NodeKey core) ∉ (slhGraph core pkSeed).ch κ := by
  intro h
  rw [slhGraph_ch, List.mem_filterMap] at h
  obtain ⟨(b | b), hb, hcb⟩ := h
  · obtain ⟨_, -, -, h⟩ := (childCell_inl_eq_some_iff core).1 hcb
    cases h
  · obtain ⟨_, hmem, hkey, h⟩ := (childCell_inr_eq_some_iff core).1 hcb
    cases h
    obtain rfl := hd.keyInjective
      (addressFacts_of_mem_constructionAddresses hd.canonicalAddressBounds hmem)
      (addressFacts_of_mem_constructionAddresses hd.canonicalAddressBounds
        rootAdrs_mem_constructionAddresses) hkey
    exact inr_rootAdrs_not_mem_childAdrs (nodeAdrs_mem_constructionAddresses core κ) hb

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- A lab XMSS node above the leaves leaves its own cell drawn at its value. -/
theorem cell_of_mem_support_labXmssNode {pkSeed : core.PkSeed} (base : Adrs) (z t : ℕ)
    (hmem : xmssNodeAdrs base (z + 1) t ∈ constructionAddresses vp)
    {s : LabState core × List (DeriveQuery core ⊕ NodeKey core)} {w}
    (hw : w ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labXmssNode core base (z + 1) t)).run s)) :
    w.2.1.2 (.inr ⟨_, _, hmem, rfl⟩) = some w.1 := by
  simp only [labXmssNode, PerfectMerkleTree.merkleRootM, xmssNodeHashWith, labH,
    labNode_of_mem core hmem, readCell, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    at hw
  obtain ⟨_, -, _, -, hw⟩ := hw
  rw [simulateQ_HasQuery_query, CanonicalGraph.deferredImpl_run_read, support_map] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hy).2

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **The root cell holds `PK.root`** at the end of every deferred run of the lab experiment. -/
theorem cell_rootNode_of_mem_support_deferredImpl_labExperiment {pkSeed : core.PkSeed}
    {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
    {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run ((∅, ∅), []))) :
    z.2.1.2 (.inr (rootNode core)) = some z.1.pk.pkRoot := by
  have hmono : ∀ {α : Type} (oa : OracleComp (labSpec core) α) (pk : PublicKeyCore core) s,
      s.1.2 (.inr (rootNode core)) = some pk.pkRoot →
        ∀ w ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl oa).run s),
          w.2.1.2 (.inr (rootNode core)) = some pk.pkRoot :=
    fun oa _ s h w hw ↦ ((slhGraph core pkSeed).le_of_mem_support_simulateQ_deferredImpl oa hw).2 h
  refine holds_of_mem_support_run_unforgeableTranscriptExperiment
    (slhGraph core pkSeed).deferredImpl
    (I := fun pk _ _ s ↦ s.1.2 (.inr (rootNode core)) = some pk.pkRoot)
    (allowed := IsAmbientLabQuery core) ?_ ?_ ?_ ?_ (labAdversary core adv pkSeed)
    (allQueriesSatisfy_labAdversary_main adv) hz
  · intro w hw
    simp only [labScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨hp', hhp⟩ : ∃ hp', vp.params.hp = hp' + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos vp.valid.hp_pos).symm⟩
    have hmem : xmssNodeAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) (hp' + 1) 0 ∈
        constructionAddresses vp := hhp ▸ rootAdrs_mem_constructionAddresses
    have hκ : rootNode core = ⟨_, _, hmem, rfl⟩ := Subtype.ext (by simp [rootNode, rootAdrs, hhp])
    rw [labKeygen, hhp] at hw'
    rw [hκ]
    exact cell_of_mem_support_labXmssNode _ _ _ hmem hw'
  · intro t _ pk _ _ s h w hw
    exact ((slhGraph core pkSeed).le_of_mem_support_deferredImpl hw).2 h
  · intro pk _ msg _ s h w hw
    exact hmono _ pk s h w hw
  · intro pk _ _ msg sig s h w hw
    exact hmono _ pk s h w hw

end Root

/-! ## The charges -/

namespace DeferredCharge

variable {vp : ValidatedParams} {core : CorePrimitives vp.params} [SampleableType core.Y]
  [DecidableEq core.Y] [SampleableType core.SkSeed] [SampleableType core.SkPrf]
  [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf] {pkSeed : core.PkSeed}

/-- A hazard of relabelled states charged to a potential bounded by `U` of the public cache, as a
further charge with no hazard of the seeds. -/
@[expose] def ofCharged (P : LabState core → Prop) (Φ : LabState core → ℝ≥0∞)
    (hP : (slhGraph core pkSeed).IsCharged P Φ) (hP₀ : ¬P (∅, ∅))
    (U : (hashSpec core).QueryCache → ℝ≥0∞) (hU : ∀ st, Φ st ≤ U st.1) :
    DeferredCharge core pkSeed where
  P := P
  Φ := Φ
  isCharged := hP
  not_empty := hP₀
  U := U
  le_U := hU
  H _ _ := False
  c := 0
  prEvent_le _ := by simp

end DeferredCharge

/-! ## The projected keys at `n = 32` -/

section Shake

variable {vp : ValidatedParams}

variable (vp) in
open Classical in
/-- The node at whose key an `H_msg` point `H_msg(PK.seed, PK.seed, ·, ·)` is read at public seed
`pkSeed`: the node at the key with the bytes of `PK.seed`, if there is one. No other point is
read at a node. -/
noncomputable def linkedNode (pkSeed : (shakeCore vp).PkSeed) :
    (hashSpec (shakeCore vp)).Domain → Option (NodeKey (shakeCore vp))
  | .inl (.hmsg R s _ _) =>
      if h : R = pkSeed ∧ s = pkSeed ∧ ∃ a ∈ constructionAddresses vp,
          (shakeCore vp).adrsToKey a = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n))
        then some ⟨_, h.2.2⟩ else none
  | _ => none

variable (vp) in
/-- An answer read as a label: the first `n` bytes of an `H_msg` answer, any other answer as is. -/
def linkedProj : (t : (hashSpec (shakeCore vp)).Domain) → (hashSpec (shakeCore vp)).Range t →
    (shakeCore vp).Y
  | .inl (.thash _ _ _) => id
  | .inl (.hmsg _ _ _ _) => prefixBytes vp.params.n
  | .inr _ => id

/-- **The projected keys of the linked points** at public seed `pkSeed`: an `H_msg` point
`H_msg(PK.seed, PK.seed, ·, ·)` is read, through its first `n` bytes, at the node at the key with
the bytes of `PK.seed`. -/
noncomputable def linkedProjKeys (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed) : (slhGraph (shakeCore vp) pkSeed).ProjKeys where
  node := linkedNode vp pkSeed
  proj := linkedProj vp
  prEvent_proj_le t k h ℓ := by
    rcases t with (_ | ⟨R, s, r, msg⟩) | _
    · simp [linkedNode] at h
    · rw [SampleableType.prEvent_uniformSample_inst_irrel _ (inferInstanceAs (SampleableType
        (Bytes vp.params.m)))]
      exact prEvent_uniformSample_prefixBytes_eq_le hnm ℓ
    · simp [linkedNode] at h

/-- Every public entry at a projected key is a cached `H_msg` point. -/
theorem encard_keyEntries_linkedProjKeys_le (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed) (C : (hashSpec (shakeCore vp)).QueryCache) :
    ((linkedProjKeys hnm pkSeed).keyEntries C).encard ≤
      {t | (C t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t}.encard := by
  refine Set.encard_le_encard fun t ⟨hC, hk⟩ ↦ ⟨hC, ?_⟩
  rcases t with (_ | _) | _
  · simp [linkedProjKeys, linkedNode] at hk
  · trivial
  · simp [linkedProjKeys, linkedNode] at hk

/-! ## The virtual hit and the honest input at a linked point, transported -/

variable {pkSeed : (shakeCore vp).PkSeed} {s : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf}
  {st : LabState (shakeCore vp)} {o : DeriveOutcome (shakeCore vp)}

private theorem fill_pkSeed (hpk : o.pk.pkSeed = pkSeed) :
    (DeriveOutcome.fill (shakeCore vp) s o).pk.pkSeed = pkSeed := by
  simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_pk, hpk]

private theorem fill_pkRoot :
    (DeriveOutcome.fill (shakeCore vp) s o).pk.pkRoot = o.pk.pkRoot := by
  simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_pk]

private theorem fill_skSeed : (DeriveOutcome.fill (shakeCore vp) s o).sk.skSeed = s.1 := by
  simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_sk, fillSecretKey]

/-- An address key with the bytes of `PK.seed` is the key read off `PK.seed`. -/
private theorem eq_adrsKeyOfList {k : (shakeCore vp).AdrsKey}
    (hks : Vector.toList (k : Bytes 32) = Vector.toList (pkSeed : Bytes vp.params.n)) :
    k = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n)) := by
  rw [adrsKeyOfList, ← hks]
  exact (bytesOfList_toList (k : Bytes 32)).symm

/-- **A virtual hit is a projected hit.** Under the key discipline, a virtual hit of the
transcript rebuilt with the seeds `s`, on the cache that the relabelled state `st` stands for at
them, is a projected hit of `st` at the projected keys of the linked points. -/
theorem projHazard_of_virtualHit_fill (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) (hpk : o.pk.pkSeed = pkSeed)
    (h : VirtualHit vp (DeriveOutcome.fill (shakeCore vp) s o,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache st))) :
    (linkedProjKeys hnm pkSeed).ProjHazard st := by
  obtain ⟨k, xs, r, rest, u, hhon, hL, hu, hx⟩ := h
  rw [fill_pkSeed hpk, fill_skSeed] at hhon
  rw [fill_pkSeed hpk] at hL hu hx
  obtain ⟨κ, vs, hκ, hpt⟩ := exists_childVals_eq_some_of_honestEntry hd hhon
  simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at hpt
  obtain ⟨rfl, rfl⟩ := hpt
  have hk := eq_adrsKeyOfList hL.2.1
  have hnode : linkedNode vp pkSeed (.inl (linkedHmsg vp pkSeed r rest)) = some κ := by
    simp only [linkedNode]
    split_ifs with hc
    · exact congrArg some (Subtype.ext hk.symm)
    · exact absurd ⟨rfl, rfl, hk ▸ κ.2⟩ hc
  refine ⟨.inl (linkedHmsg vp pkSeed r rest), κ, prefixBytes vp.params.n u, u, hnode, ?_, ?_, rfl⟩
  · exact (merge_fst_thash_of_childVals_eq_some hd.keySeparated hκ).symm.trans hx
  · exact (merge_fst_hmsg _ _ _ _).symm.trans hu

/-- **The honest input at a linked point, at a node key.** Under the key discipline, at a public
seed whose key is the key of a node `κ₀`, an honest input at a linked point of the rebuilt
transcript makes the first child cell of `κ₀` hold the value of the root cell, when that is
`PK.root`. -/
theorem pairHazard_of_linkedHonestInput_fill (hd : (shakeCore vp).KeyDiscipline vp)
    {κ₀ : NodeKey (shakeCore vp)}
    (hκ₀ : κ₀.1 = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n)))
    (hroot : st.2 (.inr (rootNode (shakeCore vp))) = some o.pk.pkRoot)
    (hpk : o.pk.pkSeed = pkSeed)
    (h : LinkedHonestInput vp (DeriveOutcome.fill (shakeCore vp) s o,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache st))) :
    ∃ c₁ cs, (slhGraph (shakeCore vp) pkSeed).ch κ₀ = c₁ :: cs ∧
      CanonicalGraph.PairHazard _ _ _ c₁ (.inr (rootNode (shakeCore vp))) st := by
  unfold LinkedHonestInput HonestInputIn at h
  rw [fill_pkSeed hpk, fill_skSeed] at h
  rcases h with ⟨(⟨s', k, _ | ⟨r, rest⟩⟩ | _), hL, hhon⟩ | ⟨a, b, -, hab, hL⟩
  · exact hL.elim
  · obtain ⟨rfl, hks, hr⟩ := hL
    rw [fill_pkSeed hpk] at hks hhon
    rw [fill_pkRoot] at hr
    obtain ⟨κ, vs, hκ, hpt⟩ := exists_childVals_eq_some_of_honestEntry hd hhon
    simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at hpt
    obtain ⟨hk, rfl⟩ := hpt
    obtain rfl : κ = κ₀ := Subtype.ext (hk.trans ((eq_adrsKeyOfList hks).trans hκ₀.symm))
    rw [CanonicalGraph.childVals_eq_some_iff] at hκ
    obtain ⟨c₁, cs, h1, -, hch⟩ := List.forall₂_cons_right_iff.1 hκ
    exact ⟨c₁, cs, hch, r, h1, hroot.trans (by rw [hr])⟩
  · exact hL.elim
  · obtain ⟨-, hks, -⟩ := hL
    exact (hd.keySeparated b (nodeAdrs (shakeCore vp) κ₀) (isSecretKey_of_inl_mem_childAdrs hab)
      (type_le_four_of_mem_constructionAddresses (nodeAdrs_mem_constructionAddresses _ κ₀))
      (by rw [adrsToKey_nodeAdrs, hκ₀]; exact eq_adrsKeyOfList hks)).elim

/-- **The honest input at a linked point, at no node key.** Under the key discipline, at a public
seed whose key is no node's key, an honest input at a linked point of the rebuilt transcript
makes the first secret seed the value of the root cell, when that is `PK.root`. -/
theorem rootSeed_of_linkedHonestInput_fill (hd : (shakeCore vp).KeyDiscipline vp)
    (hN : ¬∃ κ : NodeKey (shakeCore vp),
      κ.1 = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n)))
    (hroot : st.2 (.inr (rootNode (shakeCore vp))) = some o.pk.pkRoot)
    (hpk : o.pk.pkSeed = pkSeed)
    (h : LinkedHonestInput vp (DeriveOutcome.fill (shakeCore vp) s o,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache st))) :
    st.2 (.inr (rootNode (shakeCore vp))) = some s.1 := by
  unfold LinkedHonestInput HonestInputIn at h
  rw [fill_pkSeed hpk, fill_skSeed] at h
  rcases h with ⟨(⟨s', k, _ | ⟨r, rest⟩⟩ | _), hL, hhon⟩ | ⟨a, b, -, -, hL⟩
  · exact hL.elim
  · obtain ⟨rfl, hks, -⟩ := hL
    rw [fill_pkSeed hpk] at hks hhon
    obtain ⟨κ, vs, -, hpt⟩ := exists_childVals_eq_some_of_honestEntry hd hhon
    simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at hpt
    exact (hN ⟨κ, hpt.1.trans (eq_adrsKeyOfList hks)⟩).elim
  · exact hL.elim
  · obtain ⟨-, -, hr⟩ := hL
    rw [fill_pkRoot] at hr
    rw [hroot, ← hr]
    rfl

/-! ## The charge -/

/-- A uniform first secret seed is the value of the root cell with probability at most
`1 / |Y|`. -/
theorem prEvent_rootSeed_le (st : LabState (shakeCore vp)) :
    Pr{let s ← $ᵗ ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf)}[
      st.2 (.inr (rootNode (shakeCore vp))) = some s.1] ≤ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun _ ↦
    (prEvent_mono _ _ _ fun _ h ↦ h.symm).trans
      (SampleableType.prEvent_uniformSample_apply_eq_le (Option.some_injective _) _)

variable (pkSeed) in
open Classical in
/-- **The charge of the root** at public seed `pkSeed`, for the honest input at a linked point.
If the key with the bytes of `PK.seed` is the key of a node, two cells drawn equal, its first child
cell and the root cell, charged `1 / |Y|`; otherwise the first secret seed equal to the root cell,
charged `1 / |Y|`. -/
noncomputable def rootCharge (hd : (shakeCore vp).KeyDiscipline vp) :
    DeferredCharge (shakeCore vp) pkSeed :=
  if h : ∃ κ : NodeKey (shakeCore vp),
      κ.1 = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n)) then
    match hch : (slhGraph (shakeCore vp) pkSeed).ch h.choose with
    | [] => .ofSeed (fun _ _ ↦ False) 0 fun _ ↦ by simp
    | c₁ :: _ => .ofCharged _ _ (CanonicalGraph.isCharged_pairHazard (c₁ := c₁)
        (c₂ := .inr (rootNode (shakeCore vp))) _ fun he ↦
        inr_rootNode_not_mem_ch hd pkSeed h.choose (by rw [hch, ← he]; exact List.mem_cons_self))
        CanonicalGraph.not_pairHazard_empty (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
        CanonicalGraph.pairPotential_le
  else
    { P := fun _ ↦ False
      Φ := 0
      isCharged := CanonicalGraph.isCharged_false _
      not_empty := id
      U := 0
      le_U := fun _ ↦ le_rfl
      H := fun s st ↦ st.2 (.inr (rootNode (shakeCore vp))) = some s.1
      c := fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹
      prEvent_le := prEvent_rootSeed_le }

/-- The root is charged at most `1 / |Y|` in all. -/
theorem rootCharge_U_add_c_le (hd : (shakeCore vp).KeyDiscipline vp)
    (C : (hashSpec (shakeCore vp)).QueryCache) :
    (rootCharge pkSeed hd).U C + (rootCharge pkSeed hd).c C ≤
      (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ := by
  unfold rootCharge
  split_ifs with h
  · split <;> simp [DeferredCharge.ofSeed, DeferredCharge.ofCharged]
  · simp

/-- **The root charges the honest input at a linked point.** -/
theorem rootCharge_of_linkedHonestInput_fill (hd : (shakeCore vp).KeyDiscipline vp)
    (hroot : st.2 (.inr (rootNode (shakeCore vp))) = some o.pk.pkRoot)
    (hpk : o.pk.pkSeed = pkSeed)
    (h : LinkedHonestInput vp (DeriveOutcome.fill (shakeCore vp) s o,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache st))) :
    (rootCharge pkSeed hd).P st ∨ (rootCharge pkSeed hd).H s st := by
  unfold rootCharge
  split_ifs with hN
  · split
    · next hch =>
      obtain ⟨_, _, hch', -⟩ := pairHazard_of_linkedHonestInput_fill hd hN.choose_spec hroot hpk h
      exact (List.cons_ne_nil _ _ (hch'.symm.trans hch)).elim
    · next c₁ cs hch =>
      obtain ⟨_, _, hch', hP⟩ := pairHazard_of_linkedHonestInput_fill hd hN.choose_spec hroot hpk h
      obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 (hch.symm.trans hch')
      exact .inl hP
  · exact .inr (rootSeed_of_linkedHonestInput_fill hd hN hroot hpk h)

variable (pkSeed) in
/-- **The charge of the virtual hit and the honest input at a linked point** at public seed
`pkSeed`: projected hits at the projected keys of the linked points, charged once per entry,
with the charge of the root. -/
noncomputable def linkedCharge (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) : DeferredCharge (shakeCore vp) pkSeed :=
  (DeferredCharge.ofCharged _ _ (linkedProjKeys hnm pkSeed).isCharged
    CanonicalGraph.ProjKeys.not_projHazard_empty
    (fun C ↦ (((linkedProjKeys hnm pkSeed).keyEntries C).encard : ℝ≥0∞) /
      Nat.card (shakeCore vp).Y) CanonicalGraph.ProjKeys.potential_le).add
    (rootCharge pkSeed hd)

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- **The virtual hit and the honest input at a linked point are charged** to `linkedCharge`, for
every adversary. -/
theorem charges_linkedCharge (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m)
    (A : UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))) :
    (linkedCharge pkSeed hd hnm).Charges A fun z ↦ VirtualHit vp z ∨ LinkedHonestInput vp z := by
  intro w hw h _
  obtain ⟨hz, hst, -⟩ := (CanonicalGraph.mem_support_deferredFillDraw_iff _).1 hw
  have hpk := (hiddenUndrawn_of_mem_support_deferredImpl_labExperiment pkSeed hd A hz).1
  have hroot := (RelabelState.le_of_mem_support_endFill hst).2
    (cell_rootNode_of_mem_support_deferredImpl_labExperiment A hz)
  refine .inr (.inr ?_)
  rcases h with h | h
  · exact .inl (.inl (projHazard_of_virtualHit_fill hd hnm hpk h))
  · exact (rootCharge_of_linkedHonestInput_fill hd hroot hpk h).imp .inr .inr

/-! ## The budget -/

/-- On every deferred run of the lab experiment, for an adversary with hash budget `qh` and
signing budget `qs`: the public entries at node keys and the cached derivable public points
number at most `qh + V`, and with the cached `H_msg` points at most `qh + qs + V`. -/
private theorem encard_le_of_mem_support {A : UnforgeableAdversary
      (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))} {qh qs : ℕ}
    (hsep : (shakeCore vp).KeySeparated) (hA : A.RomQueryBound qh qs)
    {z : DeriveOutcome (shakeCore vp) × LabState (shakeCore vp) ×
      List (DeriveQuery (shakeCore vp) ⊕ NodeKey (shakeCore vp))}
    (hz : z ∈ support ((simulateQ (slhGraph (shakeCore vp) pkSeed).deferredImpl
      (labExperiment (shakeCore vp) A pkSeed)).run ((∅, ∅), []))) :
    ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard +
        {t | (z.2.1.1 t).isSome ∧
          IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard ≤
      qh + GeneralScheme.verifyInternalQueryBound vp.params ∧
    ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard +
        {t | (z.2.1.1 t).isSome ∧
          IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard +
        {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t}.encard ≤
      qh + qs + GeneralScheme.verifyInternalQueryBound vp.params := by
  refine ⟨encard_keyEntries_add_encard_setOf_isDerivablePublicQuery_le hsep hA hz, ?_⟩
  have hABH : Disjoint ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1 ∪
      {t | (z.2.1.1 t).isSome ∧ IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))})
      {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t} := by
    refine Set.disjoint_left.2 fun t ht ⟨_, hh⟩ ↦ ?_
    rcases t with (_ | ⟨R, s, r, m⟩) | _
    · exact hh.elim
    · rcases ht with ⟨_, hk⟩ | ⟨_, hd⟩
      · rw [slhNodeKeys_node_eq_none_of_forall_ne_thash _ (by simp)] at hk; cases hk
      · exact hd
    · exact hh.elim
  rw [← Set.encard_union_eq (disjoint_keyEntries_setOf_isDerivablePublicQuery hsep pkSeed _),
    ← Set.encard_union_eq hABH]
  refine (Set.encard_le_encard (t := {t | (z.2.1.1 t).isSome})
    (by rintro t ((⟨hC, _⟩ | ⟨hC, _⟩) | ⟨hC, _⟩) <;> exact hC)).trans ?_
  simpa using (slhGraph (shakeCore vp) pkSeed)
    |>.encard_inter_setOf_isSome_le_add_of_mem_support_simulateQ_deferredImpl (D := Set.univ)
    (p := IsPublicLabQuery (shakeCore vp)) (fun _ _ ↦ trivial)
    (isQueryBoundP_labExperiment_public pkSeed hA) hz

/-- The joint budget with the linked charge, the root charged `1 / |Y|`: twice the public entries
at node keys, the projected entries, the cached derivable public points and one, over `|Y|`, plus
the further charge `c₀`. -/
private theorem budget_linkedCharge_le (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) (c₀ : (hashSpec (shakeCore vp)).QueryCache → ℝ≥0∞)
    (C : (hashSpec (shakeCore vp)).QueryCache) :
    2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries C).encard : ℝ≥0∞) /
          Nat.card (shakeCore vp).Y + (linkedCharge pkSeed hd hnm).U C +
        (seedCharge (shakeCore vp) pkSeed C + (c₀ C + (linkedCharge pkSeed hd hnm).c C)) ≤
      (2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries C).encard : ℝ≥0∞) +
          ((linkedProjKeys hnm pkSeed).keyEntries C).encard +
          {t | (C t).isSome ∧ IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard +
          1) / Nat.card (shakeCore vp).Y + c₀ C := by
  have hc := rootCharge_U_add_c_le (pkSeed := pkSeed) hd C
  simp only [linkedCharge, DeferredCharge.add, DeferredCharge.ofCharged, Pi.add_apply, zero_add,
    seedCharge, ENNReal.div_eq_inv_mul]
  calc _ = (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ *
          (2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries C).encard : ℝ≥0∞) +
            ((linkedProjKeys hnm pkSeed).keyEntries C).encard +
            {t | (C t).isSome ∧
              IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard) + c₀ C +
        ((rootCharge pkSeed hd).U C + (rootCharge pkSeed hd).c C) := by ring
    _ ≤ _ + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by ring

/-- **The budget of the linked charge with the `H_msg` charge.** Under key separation, for an
adversary with hash budget `qh` and signing budget `qs`, on every deferred run of the lab
experiment, the joint budget with the linked charge and the charge of the message-`PRF` key is at
most `(2 (qh + V) + 2 qs + 2) / |Y|`: each projected entry is a cached `H_msg` point. -/
theorem withinBudget_linkedCharge_of_romQueryBound (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) {A : UnforgeableAdversary
      (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))} {qh qs : ℕ}
    (hA : A.RomQueryBound qh qs) :
    (linkedCharge pkSeed hd hnm).WithinBudget A
      (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) + 2 * qs + 2) /
        Nat.card (shakeCore vp).Y) := fun z hz ↦ by
  obtain ⟨-, h2⟩ := encard_le_of_mem_support hd.keySeparated hA hz
  have hL := encard_keyEntries_linkedProjKeys_le hnm pkSeed z.2.1.1
  refine (budget_linkedCharge_le (pkSeed := pkSeed) hd hnm
    (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹) z.2.1.1).trans ?_
  rw [hmsgCharge, inv_eq_one_div, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  gcongr ?_ / _
  set a := ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard
  set b := {t | (z.2.1.1 t).isSome ∧
    IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard
  set h := {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t}.encard
  have hR := ENat.toENNReal_le.2 <| show
      2 * a + ((linkedProjKeys hnm pkSeed).keyEntries z.2.1.1).encard + b + h ≤
        2 * (qh + qs + GeneralScheme.verifyInternalQueryBound vp.params) from
    calc _ ≤ 2 * a + h + b + h := by gcongr
      _ ≤ 2 * a + h + b + h + b := le_self_add
      _ = 2 * (a + b + h) := by ring
      _ ≤ _ := by gcongr
  push_cast at hR
  calc _ = 2 * (a : ℝ≥0∞) + ((linkedProjKeys hnm pkSeed).keyEntries z.2.1.1).encard + b + h +
        2 := by ring
    _ ≤ _ := add_le_add_left hR 2
    _ = _ := by ring

/-- **The budget of the linked charge with the fixed-key charge.** Under key separation, for an
adversary with hash budget `qh` and signing budget `qs`, on every deferred run of the lab
experiment, the joint budget with the linked charge and the fixed-key charge `1 / |Y|` is at most
`(2 (qh + V) + qs + 2) / |Y|`: each projected entry is a cached `H_msg` point. -/
theorem withinBudget_linkedCharge_of_romQueryBound_hedged (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) {A : UnforgeableAdversary
      (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))} {qh qs : ℕ}
    (hA : A.RomQueryBound qh qs) :
    (linkedCharge pkSeed hd hnm).WithinBudget A
      (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) + qs + 2) /
        Nat.card (shakeCore vp).Y) := fun z hz ↦ by
  obtain ⟨h1, h2⟩ := encard_le_of_mem_support hd.keySeparated hA hz
  have hL := encard_keyEntries_linkedProjKeys_le hnm pkSeed z.2.1.1
  refine (budget_linkedCharge_le (pkSeed := pkSeed) hd hnm
    (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹) z.2.1.1).trans ?_
  rw [inv_eq_one_div, ENNReal.div_add_div_same]
  gcongr ?_ / _
  set a := ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard
  set b := {t | (z.2.1.1 t).isSome ∧
    IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard
  set h := {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t}.encard
  have hR := ENat.toENNReal_le.2 <| show
      2 * a + ((linkedProjKeys hnm pkSeed).keyEntries z.2.1.1).encard + b ≤
        (qh + GeneralScheme.verifyInternalQueryBound vp.params) +
          (qh + qs + GeneralScheme.verifyInternalQueryBound vp.params) from
    calc _ ≤ 2 * a + h + b := by gcongr
      _ ≤ 2 * a + h + b + b := le_self_add
      _ = (a + b) + (a + b + h) := by ring
      _ ≤ _ := add_le_add h1 h2
  push_cast at hR
  calc _ = 2 * (a : ℝ≥0∞) + ((linkedProjKeys hnm pkSeed).keyEntries z.2.1.1).encard + b +
        2 := by ring
    _ ≤ _ := add_le_add_left hR 2
    _ = _ := by ring

/-- **The budget of the linked charge for the verifying adversary**, with the `H_msg` charge:
the joint budget of the message-`PRF` key at budget `(qh + V, qs)` plus `(qs + 1) / |Y|`. -/
theorem withinBudget_linkedCharge (hd : (shakeCore vp).KeyDiscipline vp)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    (linkedCharge pkSeed hd hnm).WithinBudget (verifyingAdv vp h32.le hnm adv)
      (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp.params) + qs + 1) /
        Nat.card (shakeCore vp).Y + ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y) :=
  fun z hz ↦ (withinBudget_linkedCharge_of_romQueryBound hd hnm
    (romQueryBound_verifyingAdv h32.le hnm hadv) z hz).trans_eq <| by
      rw [ENNReal.div_add_div_same]
      congr 1
      push_cast
      ring

/-- **The budget of the linked charge for the verifying adversary**, with the fixed-key charge:
the joint budget of the fixed key at budget `(qh + V, qs)` plus `(qs + 1) / |Y|`. -/
theorem withinBudget_linkedCharge_hedged (hd : (shakeCore vp).KeyDiscipline vp)
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    (linkedCharge pkSeed hd hnm).WithinBudget (verifyingAdv vp h32.le hnm adv)
      (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      ((2 * ((qh : ℝ≥0∞) + 2 * GeneralScheme.verifyInternalQueryBound vp.params) + 1) /
        Nat.card (shakeCore vp).Y + ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y) :=
  fun z hz ↦ (withinBudget_linkedCharge_of_romQueryBound_hedged hd hnm
    (romQueryBound_verifyingAdv h32.le hnm hadv) z hz).trans_eq <| by
      rw [ENNReal.div_add_div_same]
      congr 1
      push_cast
      ring

/-! ## The advantage -/

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at every public seed.** At `n = 32` and
`n ≤ m`, under the canonical address bounds, for every public seed `pkSeed`, every `opt_rand`
distribution and an adversary with hash budget `qh` and signing budget `qs`, the advantage of the
adversary against `shakeRomScheme` at `pkSeed` is at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + (qs + 1) / |Y|`, with `V` the
verifier's query bound. -/
theorem shakeAdvantage_pure_le_securityBound_add_of_n_eq_32
    (hb : CanonicalAddressBounds vp.params) (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
          (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y +
        ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y :=
  shakeAdvantage_pure_le_securityBound_add hb h32 hnm adv hadv
    (linkedCharge pkSeed (keyDiscipline_shakePrimitives vp hb) hnm) _
    (div_natCard_ne_top (by simp)) (charges_linkedCharge _ hnm _)
    (withinBudget_linkedCharge _ h32 hnm adv hadv)

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at every public seed, hedged form.** As
`shakeAdvantage_pure_le_securityBound_add_of_n_eq_32`, with `optRand pk` equal to `PK.seed` with
probability at most `ε` at every public key: the advantage is at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y| +
(qs + 1) / |Y|`. -/
theorem shakeAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged
    (hb : CanonicalAddressBounds vp.params) (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε) :
    shakeAdvantage vp adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
          (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        1 / Nat.card (shakeCore vp).Y +
        qs * ε * (((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) : ℝ≥0∞) + qs +
          1) / Nat.card (shakeCore vp).Y + ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y :=
  shakeAdvantage_pure_le_securityBound_add_hedged hb h32 hnm adv hadv hε
    (linkedCharge pkSeed (keyDiscipline_shakePrimitives vp hb) hnm) _
    (div_natCard_ne_top (by simp)) (charges_linkedCharge _ hnm _)
    (withinBudget_linkedCharge_hedged _ h32 hnm adv hadv)

end Shake

end SLHDSA.Security
