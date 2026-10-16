/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Commutativity
public import VCVio.Quantum.Oracle.Compressed.CollisionRuntime

/-!
# Recording grades and time-dependent coherent comparisons

The recording population counts occupied commitment keys, counting all split cells at a key
only once. The extraction-controlled swap preserves this population and fixes the empty record.
These are the recording-register ingredients of ePrint 2025/2166, Definition 9.8 and
Lemmas 9.10–9.12, pp. 66–67, used in the online comparison of Lemma 9.7, pp. 65–69.

The population is a basis-support grade, so its use does not measure a coherent record key.
The joint database/record cost in the bounds note, equation (30), requires charging ordinary
calls and recording calls to the same budget.

Grade-restricted squared port bounds lift to coherent input mass and to the actual query
prefixes. Their time-dependent sum gives both square-root event comparisons, with the first
execution's selected mass in both directions. Identifying those ports with the
extraction-controlled recording swap is a separate operator obligation.
-/

public section

open Matrix
open scoped Kronecker ENNReal ComplexOrder

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

/-- Equality off the unsplit queried cell after swapping is equality off the selected split
cell before swapping. This identifies the spectator registers in recording conjugacy. -/
theorem swap_rest_eq_iff (s : S) (q : TpIC k Cm) (R R' : RecReg k Cm Dm Cell) :
    ((∀ p, p ≠ q → (swap ME s R).1 p = (swap ME s R').1 p) ∧
      (swap ME s R).2 = (swap ME s R').2) ↔
    (R.1 = R'.1 ∧ ∀ qt : TpICD k Cm Dm,
      qt ≠ ⟨q, ME.extract q s⟩ → R.2 qt = R'.2 qt) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨funext fun p ↦ ?_, fun qt hqt ↦ ?_⟩
    · simpa [swap] using congrFun h₂ ⟨p, ME.extract p s⟩
    · obtain ⟨p, t⟩ := qt
      by_cases ht : t = ME.extract p s
      · subst ht
        exact h₁ p (fun hp ↦ hqt (by subst hp; rfl))
      · simpa [swap, ht] using congrFun h₂ ⟨p, t⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p hp ↦ ?_, funext fun qt ↦ ?_⟩
    · exact h₂ ⟨p, ME.extract p s⟩ fun he ↦ hp (congrArg Sigma.fst he)
    · obtain ⟨p, t⟩ := qt
      by_cases ht : t = ME.extract p s
      · simp [swap, ht, h₁]
      · have hn : (⟨p, t⟩ : TpICD k Cm Dm) ≠ ⟨q, ME.extract q s⟩ := by
          intro he
          have hp := congrArg Sigma.fst he
          subst hp
          exact ht (eq_of_heq (Sigma.mk.inj he).2)
        simpa [swap, ht] using h₂ ⟨p, t⟩ hn


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

/-- A cell-controlled matrix entry changes only the selected cell and the response. -/
theorem cellControlled_apply (eR : Rg ≃ (K → Cell) × G) (β : Q × S → K)
    (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (a b : (Q × Yr) × (S × Rg)) :
    cellControlled eR β U a b =
      if a.1.1 = b.1.1 ∧ a.2.1 = b.2.1 ∧
        (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦ (eR a.2.2).1 j) =
          (fun j : {j // j ≠ β (a.1.1, a.2.1)} ↦ (eR b.2.2).1 j) ∧
        (eR a.2.2).2 = (eR b.2.2).2 then
          U (a.1.2, (eR a.2.2).1 (β (a.1.1, a.2.1)))
            (b.1.2, (eR b.2.2).1 (β (a.1.1, a.2.1))) else 0 := by
  rw [cellControlled, labelControlled_apply, onFactor_apply]
  simp only [cellSplit, Equiv.coe_fn_mk, Prod.mk.injEq]

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

/-! ## Grade-sensitive weights on actual prefixes -/

namespace QuerySupportedOn

/-- Tracing out the unused workspace preserves a grade read from the private register. -/
theorem callInput {A J E D Z : Type*} [Fintype A] [Fintype J] [Fintype E] [Fintype D]
    [DecidableEq A] [DecidableEq J] [DecidableEq E] [DecidableEq D]
    {g : D → Z} {T : Set Z} {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × D ↦ g m.2) T ρ) (ℓ : A ≃ J × E) :
    QuerySupportedOn (fun m : J × D ↦ g m.2) T (QuantumRuntime.callInput ℓ D ρ) := by
  intro a b hab
  simp only [QuantumRuntime.callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
    SubInstrument.relabel_branch_apply, submatrix_apply] at hab
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact hρ _ _ he

end QuerySupportedOn

namespace QuantumRuntime

universe uL vL uP vP w

variable {spec : QuantumOracleSpec.{uP, vP}} {L : LocalSig.{uL, vL}}
  (R : QuantumRuntime spec) (I : L.Interp) (g : R.D → ℕ)

/-- A local comparison needed only on grade `t+j` bounds the weight of the actual `j`-th
query from an input of grade `t`. All intervening local instruments and query outcomes are
included. The hypothesis is on one-step operators, not on complete executions. -/
theorem queryWeight_mono_of_grade
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    {w w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    {W : QReg → Type w} {A : QReg} (x : QuantumComp L spec W A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (t j : ℕ)
    (hgrade : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ)
    (hw : ∀ i σ, σ.PosSemidef →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic (t + j)) σ →
        w i σ ≤ w' i σ) :
    R.queryWeight I w x ρ j ≤ R.queryWeight I w' x ρ j := by
  induction x using QuantumComp.inductionOn generalizing t j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact ENNReal.tsum_le_tsum fun b ↦
      ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) t j
        (hgrade.amplify_snd _) hw
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      exact hw i _ (posSemidef_callInput ℓ hρ) (by simpa using hgrade.callInput ℓ)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine ENNReal.tsum_le_tsum fun r ↦
        ih r ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) (t + 1) j
          (QuerySupportedOn.queryStep_of_step R g hR i E ℓ r hgrade) ?_
      simpa only [Nat.add_assoc, Nat.add_comm 1] using hw

end QuantumRuntime

namespace EmulatedOracle

section chargedComparison

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (E : EmulatedOracle P In)

/-- Portwise squared operator bounds lift to coherent selected mass on a supported input.
The private projector may depend on the query position; no measurement of its grade or of
its coherent port index is performed. -/
theorem ofReal_trace_coherentBlocks_conj_le_selectedMass
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (P₀ : Matrix E.S E.S ℂ) (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p,
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ P₀))ᴴ * (C p * (1 ⊗ₖ P₀))).PosSemidef)
    {σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ} (hσ : σ.PosSemidef)
    (hsupp : MatrixMap.conj ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀) σ = σ) :
    ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re ≤
      ENNReal.ofReal r * E.selectedMass selected σ := by
  let B := fun p ↦ C p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ P₀)
  have hb := posSemidef_coherentBlocks hC
  change (coherentBlocks ((fun p ↦ (if selected p then r else 0) • 1) -
    (fun p ↦ (B p)ᴴ) * B)).PosSemidef at hb
  rw [coherentBlocks_sub, coherentBlocks_mul, coherentBlocks_adjoint] at hb
  have he : coherentBlocks B = coherentBlocks C *
      ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀) := by
    change coherentBlocks (C * (fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ P₀)) = _
    rw [coherentBlocks_mul, coherentBlocks_database]
  rw [he] at hb
  have ht := ofReal_trace_conj_le
    (coherentBlocks C * ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ P₀))
    (selectedCharge selected r) (r := 1) (by norm_num)
    (by simpa only [one_smul, selectedCharge] using hb) hσ
  rw [MatrixMap.conj_mul, LinearMap.comp_apply, hsupp] at ht
  simpa only [ENNReal.ofReal_one, one_mul, E.ofReal_trace_selectedCharge selected hr hσ]
    using ht

/-- A grade-restricted squared port bound controls the discrepancy weight at an actual query
prefix by its selected coherent input mass. The bound is tested at grade `t+j`, so it can
vary with time without changing the execution or measuring the recording register. -/
theorem queryWeight_conj_le_selectedMass_of_grade
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec In) W A) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) (t j : ℕ)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic t) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p,
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ t + j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦
          if g d ≤ t + j then (1 : ℂ) else 0))).PosSemidef) :
    E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ≤
      ENNReal.ofReal r * E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ E.selectedMass selected σ) x ρ j := by
  rw [← QuantumRuntime.queryWeight_const_mul]
  refine E.coherent.toRuntime.queryWeight_mono_of_grade I g
    (E.coherent.querySupportedOn_toRuntime_step g (E.coherent_U_grade g hE))
    x hρ t j hgrade fun _ σ hσ hsupp ↦ ?_
  refine E.ofReal_trace_coherentBlocks_conj_le_selectedMass C _ selected hr hC hσ ?_
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  exact hsupp.conj_diagonal_eq_self fun m hm ↦ by simp [Set.mem_Iic.mp hm]

/-- A time-dependent family of grade-restricted port bounds accumulates against the actual
selected query mass. This is the Cauchy–Schwarz step of the online hybrid, before identifying
the discrepancy operators with a recording-swap comparison. -/
theorem tsum_rpow_queryWeight_conj_le_of_grade
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (selected : P → Bool) (r : ℕ → ℝ) (hr : ∀ j < t, 0 ≤ r j)
    (hC : ∀ j < t, ∀ p,
      ((if selected p then r j else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))).PosSemidef) :
    ∑' j, E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ^
          (2⁻¹ : ℝ) ≤
      ((∑ j ∈ Finset.range t, ENNReal.ofReal (r j)) *
        E.selectedTotalMass I selected x ρ) ^ (2⁻¹ : ℝ) := by
  let m := fun j ↦ E.coherent.toRuntime.queryWeight I
    (fun _ σ ↦ E.selectedMass selected σ) x ρ j
  have hz : ∀ j ∉ Finset.range t,
      E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ^
          (2⁻¹ : ℝ) = 0 := by
    intro j hj
    rw [E.coherent.toRuntime.queryWeight_eq_zero_of_isQueryBound I hx Finset.univ
      (by simp) (by simpa using hj) ρ, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz]
  calc
    _ ≤ ∑ j ∈ Finset.range t, ENNReal.ofReal (r j) ^ (2⁻¹ : ℝ) * m j ^ (2⁻¹ : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact E.queryWeight_conj_le_selectedMass_of_grade g hE I x hρ 0 j hgrade C selected
        (hr j (Finset.mem_range.mp hj)) (by simpa using hC j (Finset.mem_range.mp hj))
    _ ≤ _ := by
      refine (ENNReal.inner_le_Lp_mul_Lq _ _ _ Real.HolderConjugate.two_two).trans ?_
      simp only [rpow_inv_two_rpow_two, one_div]
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      gcongr
      rw [← E.tsum_queryWeight_selectedMass I selected x ρ]
      exact ENNReal.sum_le_tsum _

/-- Both square-root event comparisons follow from graded portwise squared difference
bounds. The two directions use the selected mass of the first, actual execution. The second
runtime has the same initialization and coherent block steps given by `V`; arbitrary local
instruments, observations, and subnormalized workspace inputs are allowed. -/
theorem outcomeLawWith_rpow_bounds_of_graded_ports
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    (V : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (s₁ : Unit → SubInstrument (cohIn In × E.S) (cohIn In × E.S) Unit)
    (hV : ∀ i a, (s₁ i).branch a = MatrixMap.conj (coherentBlocks V))
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t)
    (ρ : SubState A)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ E.init.matrix))
    (selected : P → Bool) (r : ℕ → ℝ) (hr : ∀ j < t, 0 ≤ r j)
    (hC : ∀ j < t, ∀ p,
      ((if selected p then r j else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        ((E.U p - V p) * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))ᴴ *
          ((E.U p - V p) *
            (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))).PosSemidef)
    {γ : Type*} [MeasurableSpace γ] (f : (Σ B, W B) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    let p₀ := E.coherent.toRuntime.outcomeLawWith I x ρ f s
    let p₁ := (QuantumRuntime.mk E.S E.init s₁).outcomeLawWith I x ρ f s
    let err := ((∑ j ∈ Finset.range t, ENNReal.ofReal (r j)) *
      E.selectedTotalMass I selected x (ρ.matrix ⊗ₖ E.init.matrix)) ^ (2⁻¹ : ℝ)
    p₀ ^ (2⁻¹ : ℝ) ≤ p₁ ^ (2⁻¹ : ℝ) + err ∧
      p₁ ^ (2⁻¹ : ℝ) ≤ p₀ ^ (2⁻¹ : ℝ) + err := by
  have hb := E.tsum_rpow_queryWeight_conj_le_of_grade g hE I hx
    (ρ.prod E.init).posSemidef hgrade (E.U - V) selected r hr hC
  rw [SubState.matrix_prod] at hb
  have hw : (QuantumRuntime.krausWeight (spec := cohSpec In) (D := E.S)
      (fun (i a : Unit) ↦ E.coherent.U i - coherentBlocks V)) =
      (fun (_ : Unit) σ ↦
        ENNReal.ofReal (MatrixMap.conj (coherentBlocks (E.U - V)) σ).trace.re) := by
    funext i σ
    cases i
    simp only [QuantumRuntime.krausWeight, tsum_fintype, Fintype.sum_unique,
      coherentBlocks_sub]
    rfl
  have h₀ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le I E.init
    E.coherent.toRuntime_step_branch hV x ρ f hs
  have h₁ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I E.init
    E.coherent.toRuntime_step_branch hV x ρ f hs
  rw [hw] at h₀ h₁
  exact ⟨h₀.trans (add_le_add le_rfl hb), h₁.trans (add_le_add le_rfl hb)⟩

end chargedComparison

end EmulatedOracle

end Quantum
