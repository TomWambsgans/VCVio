/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Commutativity

/-!
# Recording population and the extraction-controlled swap

The recording population counts occupied commitment keys, counting all split cells at a key
only once. The extraction-controlled swap preserves this population and fixes the empty record.
These are the recording-register ingredients of ePrint 2025/2166, Definition 9.8 and
Lemmas 9.10–9.12, pp. 66–67, used in the online comparison of Lemma 9.7, pp. 65–69.

The population is a basis-support grade, so its use does not measure a coherent record key.
The joint database/record cost in the bounds note, equation (30), requires charging ordinary
calls and recording calls to the same budget.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

namespace RecReg

variable {k : ℕ} {Cm Cell : Type*} {Dm : Fin k → Type*}

section population

variable [Fintype Cm] [∀ i, Fintype (Dm i)]

/-- The occupied keys, including both the unsplit cell and every split cell at that key. -/
@[expose]
noncomputable def occupied (bot : Cell) (R : RecReg k Cm Dm Cell) : Finset (TpIC k Cm) :=
  open Classical in
  Finset.univ.filter fun q ↦ R.1 q ≠ bot ∨ ∃ t, R.2 ⟨q, t⟩ ≠ bot

/-- Membership in the occupied-key set. -/
@[simp]
theorem mem_occupied (bot : Cell) (R : RecReg k Cm Dm Cell) (q : TpIC k Cm) :
    q ∈ occupied bot R ↔ R.1 q ≠ bot ∨ ∃ t, R.2 ⟨q, t⟩ ≠ bot := by
  classical
  simp [occupied]

/-- The number of occupied keys of a recording register. -/
@[expose]
noncomputable def population (bot : Cell) (R : RecReg k Cm Dm Cell) : ℕ :=
  (occupied bot R).card

/-- An empty record has no occupied keys, also when the key type is empty. -/
@[simp]
theorem occupied_const (bot : Cell) :
    occupied bot (const bot : RecReg k Cm Dm Cell) = ∅ := by
  classical
  simp [occupied, const]

/-- An empty record has zero population. -/
@[simp]
theorem population_const (bot : Cell) :
    population bot (const bot : RecReg k Cm Dm Cell) = 0 := by
  simp [population]

/-- Changing only cells at one key increases the recording population by at most one. -/
theorem population_le_of_eq_off_key (bot : Cell) (R R' : RecReg k Cm Dm Cell)
    (q : TpIC k Cm) (h₁ : ∀ p, p ≠ q → R'.1 p = R.1 p)
    (h₂ : ∀ p, p ≠ q → ∀ t, R'.2 ⟨p, t⟩ = R.2 ⟨p, t⟩) :
    population bot R' ≤ population bot R + 1 := by
  classical
  have hsub : occupied bot R' ⊆ insert q (occupied bot R) := by
    intro p hp
    by_cases hpq : p = q
    · simp [hpq]
    · rw [Finset.mem_insert]
      right
      simpa only [mem_occupied, h₁ p hpq, h₂ p hpq] using hp
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

end population

variable [∀ i, DecidableEq (Dm i)]
  {S : Type*} (ME : MultiExtractor k Cm Dm S)

/-- Swap the unsplit cell at every key with the cell selected by extraction at that key. -/
@[expose]
def swap (s : S) (R : RecReg k Cm Dm Cell) : RecReg k Cm Dm Cell :=
  (fun q ↦ R.2 ⟨q, ME.extract q s⟩,
    fun qt ↦ if qt.2 = ME.extract qt.1 s then R.1 qt.1 else R.2 qt)

/-- Swapping twice restores all recording cells. -/
@[simp]
theorem swap_swap (s : S) (R : RecReg k Cm Dm Cell) : swap ME s (swap ME s R) = R := by
  apply Prod.ext
  · funext q
    simp [swap]
  · funext qt
    rcases qt with ⟨q, t⟩
    by_cases ht : t = ME.extract q s
    · subst ht
      simp [swap]
    · simp [swap, ht]

/-- The recording swap as an involutive basis permutation. -/
@[expose]
def swapEquiv (s : S) : Equiv.Perm (RecReg k Cm Dm Cell) where
  toFun := swap ME s
  invFun := swap ME s
  left_inv := swap_swap ME s
  right_inv := swap_swap ME s

/-- The swap fixes the all-bottom record for every private basis state. -/
@[simp]
theorem swap_const (s : S) (bot : Cell) :
    swap ME s (const bot : RecReg k Cm Dm Cell) = const bot := by
  apply Prod.ext
  · rfl
  · funext qt
    simp [swap, const]

variable [Fintype Cm] [∀ i, Fintype (Dm i)]

/-- The swap preserves the occupied keys exactly. -/
@[simp]
theorem occupied_swap (s : S) (bot : Cell) (R : RecReg k Cm Dm Cell) :
    occupied bot (swap ME s R) = occupied bot R := by
  classical
  have forward (R : RecReg k Cm Dm Cell) :
      occupied bot (swap ME s R) ⊆ occupied bot R := by
    intro q hq
    rw [mem_occupied] at hq ⊢
    rcases hq with hq | ⟨t, ht⟩
    · exact Or.inr ⟨ME.extract q s, hq⟩
    · change (if t = ME.extract q s then R.1 q else R.2 ⟨q, t⟩) ≠ bot at ht
      split_ifs at ht
      · exact Or.inl ht
      · exact Or.inr ⟨t, ht⟩
  exact Finset.Subset.antisymm (forward R) (by simpa using forward (swap ME s R))

/-- The recording population is invariant under the swap. -/
@[simp]
theorem population_swap (s : S) (bot : Cell) (R : RecReg k Cm Dm Cell) :
    population bot (swap ME s R) = population bot R := by
  simp [population]

/-- The swap acts identically on a record with no occupied keys. -/
theorem swap_eq_self_of_population_eq_zero (s : S) (bot : Cell)
    (R : RecReg k Cm Dm Cell) (h : population bot R = 0) : swap ME s R = R := by
  have hR : R = const bot := by
    have he : occupied bot R = ∅ := Finset.card_eq_zero.mp h
    have hz (q : TpIC k Cm) : R.1 q = bot ∧ ∀ t, R.2 ⟨q, t⟩ = bot := by
      have hn : q ∉ occupied bot R := by simp [he]
      simpa only [mem_occupied, not_or, not_not, not_exists] using hn
    exact Prod.ext (funext fun q ↦ (hz q).1) (funext fun qt ↦ (hz qt.1).2 qt.2)
  simp [hR]

/-- On a given recording basis state, the swap depends only on extractor outputs at occupied
keys. Thus an empty list of relevant outputs also gives an exact, constant action. -/
theorem swap_eq_of_extract_eq_on_occupied (s s' : S) (bot : Cell)
    (R : RecReg k Cm Dm Cell)
    (h : ∀ q ∈ occupied bot R, ME.extract q s = ME.extract q s') :
    swap ME s R = swap ME s' R := by
  classical
  have hz (q : TpIC k Cm) (hq : q ∉ occupied bot R) :
      R.1 q = bot ∧ ∀ t, R.2 ⟨q, t⟩ = bot := by
    simpa only [mem_occupied, not_or, not_not, not_exists] using hq
  apply Prod.ext
  · funext q
    by_cases hq : q ∈ occupied bot R
    · simp only [swap, h q hq]
    · exact ((hz q hq).2 _).trans ((hz q hq).2 _).symm
  · funext qt
    obtain ⟨q, t⟩ := qt
    by_cases hq : q ∈ occupied bot R
    · simp only [swap, h q hq]
    · simp [swap, (hz q hq).1, (hz q hq).2]

end RecReg

section locality

variable {Q Yr S Rg K Cell G : Type*} [DecidableEq Q] [DecidableEq S]
  [Fintype K] [DecidableEq K] [DecidableEq Cell] [DecidableEq G]

/-- A nonzero cell-controlled matrix entry preserves the control, private state, and all
recording cells other than the selected key. No unitarity assumption is needed. -/
theorem cellControlled_locality (eR : Rg ≃ (K → Cell) × G) (β : Q × S → K)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (a b : (Q × Yr) × (S × Rg)) (h : cellControlled eR β U a b ≠ 0) :
    a.1.1 = b.1.1 ∧ a.2.1 = b.2.1 ∧
      (∀ j, j ≠ β (a.1.1, a.2.1) → (eR a.2.2).1 j = (eR b.2.2).1 j) ∧
      (eR a.2.2).2 = (eR b.2.2).2 := by
  rw [cellControlled, labelControlled_apply] at h
  have he := eq_of_onFactor_apply_ne_zero h
  change (a.1.1, a.2.1, (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦
      (eR a.2.2).1 j), (eR a.2.2).2) =
    (b.1.1, b.2.1, (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦
      (eR b.2.2).1 j), (eR b.2.2).2) at he
  simp only [Prod.mk.injEq] at he
  exact ⟨he.1, he.2.1, fun j hj ↦ congrFun he.2.2.1 ⟨j, hj⟩, he.2.2.2⟩

end locality

section recordGrade

variable {k : ℕ} {Cm Yr S Cell : Type*} {Dm : Fin k → Type*}
  [Fintype Cm] [DecidableEq Cm] [∀ i, Fintype (Dm i)]
  [DecidableEq S] [DecidableEq Cell]

/-- A recording call preserves the private basis state and increases occupied keys by at most
one, even for a coherent input tuple. -/
theorem recordUnitary_population_le (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (a b : (TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell))
    (h : recordUnitary U a b ≠ 0) :
    a.2.1 = b.2.1 ∧ RecReg.population bot a.2.2 ≤ RecReg.population bot b.2.2 + 1 := by
  have hl := cellControlled_locality RecReg.equiv Prod.fst U a b h
  refine ⟨hl.2.1, RecReg.population_le_of_eq_off_key bot b.2.2 a.2.2 a.1.1
    hl.2.2.1 ?_⟩
  intro p _ t
  exact congrFun hl.2.2.2 ⟨p, t⟩

variable [∀ i, DecidableEq (Dm i)]

/-- Extraction-indexed recording has the same population cost as unsplit recording. -/
theorem recordMEUnitary_population_le (ME : MultiExtractor k Cm Dm S) (bot : Cell)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (a b : (TpIC k Cm × Yr) × (S × RecReg k Cm Dm Cell))
    (h : recordMEUnitary ME U a b ≠ 0) :
    a.2.1 = b.2.1 ∧ RecReg.population bot a.2.2 ≤ RecReg.population bot b.2.2 + 1 := by
  have hl := cellControlled_locality (RecReg.equiv.trans (Equiv.prodComm _ _))
    (fun p ↦ (⟨p.1, ME.extract p.1 p.2⟩ : TpICD k Cm Dm)) U a b h
  refine ⟨hl.2.1, RecReg.population_le_of_eq_off_key bot b.2.2 a.2.2 a.1.1
    (fun p _ ↦ congrFun hl.2.2.2 p) ?_⟩
  intro p hp t
  exact hl.2.2.1 ⟨p, t⟩ fun he ↦ hp (congrArg Sigma.fst he)

end recordGrade

namespace VCOracle

variable {k : ℕ} {X Y Cm Z Yr Cell : Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  {Dm : Fin k → Type} [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
  (bot : Cell) (g : E.S → ℕ)

/-- An ordinary or extraction call with a passive record increases the joint grade by at most
one if the ordinary ports increase the private grade by at most one. -/
theorem withRecReg_U_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (p : Fin k ⊕ Unit) (a b : extIn k X Y Cm Z p)
    (s r : E.S × RecReg k Cm Dm Cell)
    (h : (E.withRecReg ME code bot).U p (a, s) (b, r) ≠ 0) :
    g s.1 + RecReg.population bot s.2 ≤ g r.1 + RecReg.population bot r.2 + 1 := by
  change ((E.withExtract ME code).U p (a, s.1) (b, r.1) *
    (1 : Matrix (RecReg k Cm Dm Cell) _ ℂ) s.2 r.2) ≠ 0 at h
  have hr : s.2 = r.2 := by
    by_contra hn
    exact h (by simp [hn])
  have hu := left_ne_zero_of_mul h
  have hg : g s.1 ≤ g r.1 + 1 := by
    rcases p with i | u
    · exact hE i a b s.1 r.1 hu
    · obtain ⟨ta, za⟩ := a
      obtain ⟨tb, zb⟩ := b
      change extractUnitary ME code ((ta, za), s.1) ((tb, zb), r.1) ≠ 0 at hu
      rw [extractUnitary_apply] at hu
      split_ifs at hu with he
      · exact he.2.2 ▸ Nat.le_succ _
      · exact (hu rfl).elim
  rw [hr]
  omega

/-- Every port of the unsplit recording world raises the joint private/record grade by at most
one. This is a matrix-entry statement and preserves coherent port choice. -/
theorem withRecord_U_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    (p : (Fin k ⊕ Unit) ⊕ Unit) (a b : recIn k X Y Cm Z Yr p)
    (s r : E.S × RecReg k Cm Dm Cell)
    (h : (E.withRecord ME code bot U hU).U p (a, s) (b, r) ≠ 0) :
    g s.1 + RecReg.population bot s.2 ≤ g r.1 + RecReg.population bot r.2 + 1 := by
  rcases p with p | u
  · exact withRecReg_U_grade E ME code bot g hE p a b s r h
  · obtain ⟨he, hp⟩ := recordUnitary_population_le bot U (a, s) (b, r) h
    dsimp at he hp
    rw [he]
    omega

/-- Every port of the extraction-indexed recording world has the same joint grade bound. -/
theorem withRecordME_U_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    (p : (Fin k ⊕ Unit) ⊕ Unit) (a b : recIn k X Y Cm Z Yr p)
    (s r : E.S × RecReg k Cm Dm Cell)
    (h : (E.withRecordME ME code bot U hU).U p (a, s) (b, r) ≠ 0) :
    g s.1 + RecReg.population bot s.2 ≤ g r.1 + RecReg.population bot r.2 + 1 := by
  rcases p with p | u
  · exact withRecReg_U_grade E ME code bot g hE p a b s r h
  · obtain ⟨he, hp⟩ := recordMEUnitary_population_le ME bot U (a, s) (b, r) h
    dsimp at he hp
    rw [he]
    omega

end VCOracle

section runGrade

universe uL vL w

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (F : EmulatedOracle P In) (g : F.S → ℕ)

/-- Matrix-entry grade bounds propagate through arbitrary adaptive programs, with coherent
port choice, local instruments, and changing entangled workspaces. The input operator need
only satisfy the support hypothesis; positivity and normalization are unnecessary. -/
theorem EmulatedOracle.querySupportedOn_run_of_grade
    (hF : ∀ i a b s r, F.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec In) W A) {t n : ℕ}
    (hx : x.IsQueryBound fun _ ↦ n) (ρ : Matrix (A × F.S) (A × F.S) ℂ)
    (hρ : QuerySupportedOn (fun m : A × F.S ↦ g m.2) (Set.Iic t) ρ)
    (p : Σ B, W B) :
    QuerySupportedOn (fun m : p.1 × F.S ↦ g m.2) (Set.Iic (t + n))
      ((F.coherent.toRuntime.run I x).branch p ρ) := by
  have hstep := F.coherent.querySupportedOn_toRuntime_step g
    (fun i a b s r h ↦ F.coherent_U_grade g
      (fun i a b s r h ↦ hF i b a r s h) i a b s r h)
  simpa using QuerySupportedOn.run_of_step F.coherent.toRuntime g hstep I hx hρ p

end runGrade

section compressedGrade

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- One ordinary port increases the sum of all database sizes by at most one. -/
theorem compressedVCOracle_U_totalSize_le (i : Fin k) (a b : X × Y)
    (s r : Fin k → Database X Y)
    (h : (compressedVCOracle k X Y).U i (a, s) (b, r) ≠ 0) :
    ∑ j, (s j).size ≤ (∑ j, (r j).size) + 1 := by
  change onFactor (splitAt (X × Y) (Database X Y) i)
    (compressedOracle X Y) (a, s) (b, r) ≠ 0 at h
  rw [onFactor_apply] at h
  split_ifs at h with he
  · change (fun j : {j // j ≠ i} ↦ s j.1) = (fun j ↦ r j.1) at he
    have hi := size_le_of_compressedOracle_apply_ne_zero h
    have hj (j : Fin k) : (s j).size ≤ (r j).size + if j = i then 1 else 0 := by
      by_cases hji : j = i
      · simpa [hji] using hi
      · simp [hji, congrFun he ⟨j, hji⟩]
    simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  · exact (h rfl).elim

end compressedGrade

namespace VCOracle

universe uL vL w

variable {k : ℕ} {X Y Cm Z Yr Cell : Type}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  {Dm : Fin k → Type} [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (E : VCOracle k X Y) (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)
  (bot : Cell) (g : E.S → ℕ)

private theorem recording_initial_grade
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    {A : QReg} (ρ : SubState A) :
    QuerySupportedOn (fun m : A × (E.S × RecReg k Cm Dm Cell) ↦
      g m.2.1 + RecReg.population bot m.2.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ (E.init.matrix ⊗ₖ
        (SubState.basis (RecReg.const bot : RecReg k Cm Dm Cell)).matrix)) := by
  intro a b hab
  simp only [kroneckerMap_apply] at hab
  have hd := left_ne_zero_of_mul (right_ne_zero_of_mul hab)
  have hr := right_ne_zero_of_mul (right_ne_zero_of_mul hab)
  rw [SubState.matrix_basis, Matrix.single_apply] at hr
  split_ifs at hr with he
  · obtain ⟨ha, hb⟩ := hinit _ _ hd
    change g a.2.1 + RecReg.population bot a.2.2 ≤ 0 ∧
      g b.2.1 + RecReg.population bot b.2.2 ≤ 0
    rw [← he.1, ← he.2, RecReg.population_const]
    exact ⟨by simpa using ha, by simpa using hb⟩
  · exact (hr rfl).elim

/-- The initialized unsplit recording experiment has joint grade at most its total query
budget on every output branch, for arbitrary local operations and subnormalized inputs. -/
theorem withRecord_jointPost_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec (recIn k X Y Cm Z Yr)) W A)
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn (fun m : p.1 × (E.S × RecReg k Cm Dm Cell) ↦
      g m.2.1 + RecReg.population bot m.2.2) (Set.Iic t)
      (((E.withRecord ME code bot U hU).coherent.toRuntime.jointPost I x ρ p).matrix) := by
  have h := (E.withRecord ME code bot U hU).querySupportedOn_run_of_grade
    (fun s ↦ g s.1 + RecReg.population bot s.2)
    (withRecord_U_grade E ME code bot g hE U hU) I x hx _
    (recording_initial_grade E bot g hinit ρ (Dm := Dm)) p
  have hi : (E.withRecord ME code bot U hU).coherent.toRuntime.init.matrix =
      E.init.matrix ⊗ₖ (SubState.basis (RecReg.const bot)).matrix :=
    SubState.matrix_prod _ _
  rw [QuantumRuntime.matrix_jointPost, hi]
  simpa only [Nat.zero_add, withRecord, withRecordME, withRecReg, withExtract,
    EmulatedOracle.extend, EmulatedOracle.addRegister] using h

/-- The extraction-indexed recording experiment obeys the same joint grade, with the same
query budget and no restriction on adaptive stopping or coherent port selection. -/
theorem withRecordME_jointPost_grade
    (hE : ∀ i a b s r, E.U i (a, s) (b, r) ≠ 0 → g s ≤ g r + 1)
    (hinit : QuerySupportedOn g (Set.Iic 0) E.init.matrix)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)
    {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}
    (x : QuantumComp L (EmulatedOracle.cohSpec (recIn k X Y Cm Z Yr)) W A)
    {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) (p : Σ B, W B) :
    QuerySupportedOn (fun m : p.1 × (E.S × RecReg k Cm Dm Cell) ↦
      g m.2.1 + RecReg.population bot m.2.2) (Set.Iic t)
      (((E.withRecordME ME code bot U hU).coherent.toRuntime.jointPost I x ρ p).matrix) := by
  have h := (E.withRecordME ME code bot U hU).querySupportedOn_run_of_grade
    (fun s ↦ g s.1 + RecReg.population bot s.2)
    (withRecordME_U_grade E ME code bot g hE U hU) I x hx _
    (recording_initial_grade E bot g hinit ρ (Dm := Dm)) p
  have hi : (E.withRecordME ME code bot U hU).coherent.toRuntime.init.matrix =
      E.init.matrix ⊗ₖ (SubState.basis (RecReg.const bot)).matrix :=
    SubState.matrix_prod _ _
  rw [QuantumRuntime.matrix_jointPost, hi]
  simpa only [Nat.zero_add, withRecord, withRecordME, withRecReg, withExtract,
    EmulatedOracle.extend, EmulatedOracle.addRegister] using h

end VCOracle

end Quantum
