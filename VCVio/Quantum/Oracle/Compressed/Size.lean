/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Action
public import VCVio.Quantum.Oracle.Compressed.Equivalence

/-!
# The database grows by at most one cell per call

A call to the compressed oracle changes only the queried cell of the database
(`Quantum.eq_update_of_compressedOracle_apply_ne_zero`), so it increases the number of nonempty
cells by at most one, and the local operations of a program do not touch the database register.
For a program that makes at most `q` calls on every path, run against the compressed runtime from
the empty database, the joint state at every leaf is therefore supported on databases with at
most `q` nonempty cells (Zhandry, Crypto 2019; Chiesa, Dall'Agnol, Hu and Zheng, ePrint 2025/2166,
§4.3).

The statements hold for general programs (`Quantum.QuantumComp`): adaptive, with their own local
operations and registers, and with a final register that may depend on the outcome. The bound is
stated for the operators themselves, not only for positive ones, so it applies on every branch of
the run.

## Main definitions

* `Quantum.SupportedIn S ρ`: the nonzero entries of the operator `ρ` sit between basis states
  in the set `S`.
* `Quantum.DatabaseSupportedOn t ρ`: the condition `P_t` of ePrint 2025/2166 on an operator on
  `M × Database X Y`, support on databases with at most `t` nonempty cells.

## Main results

* `Quantum.DatabaseSupportedOn.queryStep_compressedRuntime`: one call takes `P_t` to `P_(t + 1)`.
* `Quantum.DatabaseSupportedOn.run_compressedRuntime`: a program with at most `q` calls on every
  path takes `P_t` to `P_(t + q)`.
* `Quantum.forallQueries_compressedRuntime`: every call of such a program receives an operator
  supported on databases with at most `t + q - 1` nonempty cells.
* `Quantum.databaseSupportedOn_jointPost_compressedRuntime`: from the empty database, the joint
  state at every leaf satisfies `P_q`.
-/

public section

open Matrix
open scoped Kronecker

universe u v w

namespace Quantum

/-! ## Support of an operator in a set of basis states -/

section supportedIn

variable {T T' A B R : Type*}

/-- The operator `ρ` is supported in the set `S` of basis states: every nonzero entry `ρ p p'` has
`p ∈ S` and `p' ∈ S`. -/
@[expose]
def SupportedIn (S : Set T) (ρ : Matrix T T ℂ) : Prop :=
  ∀ p p', ρ p p' ≠ 0 → p ∈ S ∧ p' ∈ S

namespace SupportedIn

theorem mono {S S' : Set T} {ρ : Matrix T T ℂ} (h : SupportedIn S ρ) (hS : S ⊆ S') :
    SupportedIn S' ρ := fun p p' hp ↦ ⟨hS (h p p' hp).1, hS (h p p' hp).2⟩

theorem zero (S : Set T) : SupportedIn S (0 : Matrix T T ℂ) := fun _ _ h ↦ absurd rfl h

/-- The support condition is closed under sums of families. -/
theorem tsum {ι : Type*} {S : Set T} {f : ι → Matrix T T ℂ} (hf : ∀ i, SupportedIn S (f i)) :
    SupportedIn S (∑' i, f i) := by
  intro p p' hp
  by_cases hs : Summable f
  · rw [Matrix.tsum_apply_apply hs] at hp
    obtain ⟨i, hi⟩ := not_forall.mp fun hc : ∀ i, f i p p' = 0 ↦ hp (by simp [hc])
    exact hf i p p' hi
  · rw [tsum_eq_zero_of_not_summable hs] at hp
    exact absurd rfl hp

/-- Conjugation by `K` moves the support from `S` to `S'` when every nonzero entry `K q p` with
`p ∈ S` has `q ∈ S'`. -/
theorem conj [Fintype T] {S : Set T} {S' : Set T'} {ρ : Matrix T T ℂ} (h : SupportedIn S ρ)
    {K : Matrix T' T ℂ} (hK : ∀ q p, K q p ≠ 0 → p ∈ S → q ∈ S') :
    SupportedIn S' (MatrixMap.conj K ρ) := by
  intro q q' hq
  rw [MatrixMap.conj_apply, Matrix.mul_apply] at hq
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have hb₁ := left_ne_zero_of_mul hb
  have hb₂ := right_ne_zero_of_mul hb
  rw [Matrix.mul_apply] at hb₁
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb₁
  have hρ := h a b (right_ne_zero_of_mul ha)
  rw [Matrix.conjTranspose_apply, star_ne_zero] at hb₂
  exact ⟨hK q a (left_ne_zero_of_mul ha) hρ.1, hK q' b hb₂ hρ.2⟩

/-- A relabelling gate moves the support along the bijection. -/
theorem branch_relabel [Fintype T] [Fintype T'] [DecidableEq T] [DecidableEq T'] {S : Set T}
    {ρ : Matrix T T ℂ} (h : SupportedIn S ρ) (e : T ≃ T') :
    SupportedIn (e.symm ⁻¹' S) ((SubInstrument.relabel e).branch () ρ) := by
  intro p p' hp
  rw [SubInstrument.relabel_branch_apply, submatrix_apply] at hp
  exact h _ _ hp

/-- A map acting on the first factor preserves support in a set of values of the second
factor. -/
theorem amplify_snd {S : Set R} {ρ : Matrix (A × R) (A × R) ℂ}
    (h : SupportedIn (Prod.snd ⁻¹' S) ρ) (Φ : MatrixMap A B) :
    SupportedIn (Prod.snd ⁻¹' S) (Φ.amplify R ρ) := by
  intro p p' hp
  have hblock : ρ.submatrix (·, p.2) (·, p'.2) ≠ 0 := by
    intro h0
    rw [MatrixMap.amplify_apply, h0, map_zero] at hp
    exact hp rfl
  obtain ⟨a, b, hab⟩ : ∃ a b, ρ (a, p.2) (b, p'.2) ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hblock (Matrix.ext hc)
  exact ⟨(h _ _ hab).1, (h _ _ hab).2⟩

/-- A map acting on the first factor that moves the support from `S` to `S'` does so on the
first factor of the framed register. -/
theorem amplify_fst {S : Set A} {S' : Set B} {Φ : MatrixMap A B}
    (hΦ : ∀ σ, SupportedIn S σ → SupportedIn S' (Φ σ)) {ρ : Matrix (A × R) (A × R) ℂ}
    (h : SupportedIn (Prod.fst ⁻¹' S) ρ) : SupportedIn (Prod.fst ⁻¹' S') (Φ.amplify R ρ) := by
  rintro ⟨b, r⟩ ⟨b', r'⟩ hp
  rw [MatrixMap.amplify_apply] at hp
  exact hΦ _ (fun a a' ha ↦ h (a, r) (a', r') ha) b b' hp

end SupportedIn

end supportedIn

/-! ## Support on small databases -/

section database

variable {X Y M : Type*} [Fintype X]

/-- The condition `P_t` of ePrint 2025/2166 for operators on `M × Database X Y`: every nonzero
entry sits between databases with at most `t` nonempty cells. -/
abbrev DatabaseSupportedOn (t : ℕ) (ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ) : Prop :=
  SupportedIn {p | p.2.size ≤ t} ρ

theorem DatabaseSupportedOn.mono {t s : ℕ} {ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ}
    (h : DatabaseSupportedOn t ρ) (hts : t ≤ s) : DatabaseSupportedOn s ρ :=
  SupportedIn.mono h fun _ hp ↦ le_trans hp hts

/-- A map acting on `M` alone preserves `P_t`. -/
theorem DatabaseSupportedOn.amplify {B : Type*} {t : ℕ}
    {ρ : Matrix (M × Database X Y) (M × Database X Y) ℂ} (h : DatabaseSupportedOn t ρ)
    (Φ : MatrixMap M B) : DatabaseSupportedOn t (Φ.amplify (Database X Y) ρ) :=
  SupportedIn.amplify_snd (S := {D : Database X Y | D.size ≤ t}) h Φ

/-- An operator on `M` tensored with the empty database satisfies `P_0`. -/
theorem databaseSupportedOn_kronecker_single_empty [DecidableEq Y]
    (ρ : Matrix M M ℂ) :
    DatabaseSupportedOn 0
      (ρ ⊗ₖ Matrix.single (Database.empty : Database X Y) Database.empty (1 : ℂ)) := by
  intro p p' hp
  rw [kroneckerMap_apply] at hp
  have h := right_ne_zero_of_mul hp
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨show p.2.size ≤ 0 by rw [← he.1, Database.size_empty],
      show p'.2.size ≤ 0 by rw [← he.2, Database.size_empty]⟩
  · exact absurd rfl h

end database

/-! ## Calls to the compressed oracle -/

section compressed

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A nonzero entry of the compressed oracle relates two databases that differ at most in the
queried cell. -/
theorem eq_update_of_compressedOracle_apply_ne_zero {m m' : X × Y} {D D' : Database X Y}
    (h : compressedOracle X Y (m, D) (m', D') ≠ 0) : D = Function.update D' m'.1 (D m'.1) := by
  rw [compressedOracle_eq_controlled, controlled_mul_standardOracle_mul_controlled_apply] at h
  obtain ⟨D₁, -, hD₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hD₁ with hm
  · rw [compressAt_apply, compressAt_apply] at hD₁
    split_ifs at hD₁ with h₁ h₂
    · exact Function.eq_update_iff.mpr ⟨rfl, fun j hj ↦ (h₁ j hj).trans (h₂ j hj)⟩
    all_goals simp at hD₁
  · exact absurd rfl hD₁

/-- A nonzero entry of the compressed oracle increases the size of the database by at most
one. -/
theorem size_le_of_compressedOracle_apply_ne_zero {p p' : (X × Y) × Database X Y}
    (h : compressedOracle X Y p p' ≠ 0) : p.2.size ≤ p'.2.size + 1 :=
  (congrArg Database.size (eq_update_of_compressedOracle_apply_ne_zero h)).trans_le
    (Database.size_update_le _ _ _)

/-- A call to the compressed oracle takes `P_t` to `P_(t + 1)`. -/
theorem DatabaseSupportedOn.conj_compressedOracle {t : ℕ}
    {ρ : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ}
    (h : DatabaseSupportedOn t ρ) :
    DatabaseSupportedOn (t + 1) (MatrixMap.conj (compressedOracle X Y) ρ) :=
  SupportedIn.conj h fun _ _ hK hp ↦
    (size_le_of_compressedOracle_apply_ne_zero hK).trans (Nat.add_le_add_right hp 1)

/-- **One call.** A call of the compressed runtime, with any remainder `E` of the program
register carried along, takes `P_t` to `P_(t + 1)`. -/
theorem DatabaseSupportedOn.queryStep_compressedRuntime {A : QReg} {t : ℕ} (E : QReg)
    (ℓ : A ≃ (qromSpec X Y).In () × E) (r : (qromSpec X Y).Result ())
    {ρ : Matrix (A × Database X Y) (A × Database X Y) ℂ} (h : DatabaseSupportedOn t ρ) :
    DatabaseSupportedOn (t + 1) (((compressedRuntime X Y).queryStep () E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply]
  have h₁ : SupportedIn (Prod.fst ⁻¹' {p : (X × Y) × Database X Y | p.2.size ≤ t})
      ((SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (Database X Y))).branch () ρ) := by
    refine (h.branch_relabel _).mono fun q hq ↦ ?_
    obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (Database X Y)).surjective q
    rw [Set.mem_preimage, Equiv.symm_apply_apply] at hq
    exact hq
  have h₂ := SupportedIn.amplify_fst (R := E)
    (fun σ (hσ : DatabaseSupportedOn t σ) ↦ hσ.conj_compressedOracle) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ (Database X Y) E)).mono
    fun q hq ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ (Database X Y) E).surjective q
  rw [Set.mem_preimage, Equiv.symm_apply_apply] at hq
  exact hq

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The size invariant.** A program that makes at most `q` calls on every path, run against the
compressed runtime, takes an operator satisfying `P_t` to operators satisfying `P_(t + q)` on
every branch. -/
theorem DatabaseSupportedOn.run_compressedRuntime (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) {t : ℕ}
    {ρ : Matrix (A × Database X Y) (A × Database X Y) ℂ} (hρ : DatabaseSupportedOn t ρ)
    (p : Σ u, W u) :
    DatabaseSupportedOn (t + q) (((compressedRuntime X Y).run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn generalizing q t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Nat.le_add_right t q)
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact SupportedIn.zero _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact SupportedIn.tsum fun b ↦ ih b (fun i ↦ hx i b) (hρ.amplify _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k _).mp hx
    have hb : Function.update (fun _ : Unit ↦ q) i (q - 1) = fun _ ↦ q - 1 :=
      funext fun j ↦ by cases i; cases j; exact Function.update_self ..
    rw [hb] at hk
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine SupportedIn.tsum fun r ↦ ?_
    rw [SubInstrument.branch_toD_apply]
    cases i
    have h := ih r (hk r) (hρ.queryStep_compressedRuntime E ℓ r)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' hq] at h

/-- **The size invariant at the calls.** Every call of a program that makes at most `q` calls on
every path, run against the compressed runtime from an operator satisfying `P_t`, receives an
operator supported on databases with at most `n` nonempty cells, for any `n` with
`t + q ≤ n + 1`. -/
theorem forallQueries_compressedRuntime (I : L.Interp) {x : QuantumComp L (qromSpec X Y) W A}
    {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q) {t n : ℕ} (htn : t + q ≤ n + 1)
    {ρ : Matrix (A × Database X Y) (A × Database X Y) ℂ} (hρ : DatabaseSupportedOn t ρ) :
    (compressedRuntime X Y).ForallQueries I
      (fun _ E σ ↦ SupportedIn (Prod.fst ⁻¹' {p : (X × Y) × Database X Y | p.2.size ≤ n} :
        Set (((X × Y) × Database X Y) × E)) σ) x ρ := by
  induction x using QuantumComp.inductionOn generalizing q t with
  | pure _ _ => trivial
  | primBind _ o k ih => exact fun b ↦ ih b (fun i ↦ hx i b) htn (hρ.amplify _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k _).mp hx
    have hb : Function.update (fun _ : Unit ↦ q) i (q - 1) = fun _ ↦ q - 1 :=
      funext fun j ↦ by cases i; cases j; exact Function.update_self ..
    rw [hb] at hk
    cases i
    refine ⟨(hρ.branch_relabel _).mono fun p hp ↦ ?_, fun r ↦
      ih r (hk r) (by omega) (hρ.queryStep_compressedRuntime E ℓ r)⟩
    obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (Database X Y)).surjective p
    rw [Set.mem_preimage, Equiv.symm_apply_apply] at hp
    exact le_trans (show y.2.size ≤ t from hp) (by omega)

/-- **The size invariant from the empty database.** After a program that makes at most `q` calls
on every path, run against the compressed runtime from `ρ` and the empty database, the joint state
at every leaf is supported on databases with at most `q` nonempty cells. -/
theorem databaseSupportedOn_jointPost_compressedRuntime (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q)
    (ρ : SubState A) (p : Σ u, W u) :
    DatabaseSupportedOn q ((compressedRuntime X Y).jointPost I x ρ p).matrix := by
  rw [QuantumRuntime.matrix_jointPost]
  have h := (databaseSupportedOn_kronecker_single_empty (X := X) (Y := Y)
    ρ.matrix).run_compressedRuntime I hx p
  rwa [Nat.zero_add] at h

/-- Under `Quantum.forallQueries_compressedRuntime`, from the empty database: every call of a
program that makes at most `q` calls on every path receives an operator supported on databases
with at most `q - 1` nonempty cells. -/
theorem forallQueries_compressedRuntime_prod_init (I : L.Interp)
    {x : QuantumComp L (qromSpec X Y) W A} {q : ℕ} (hx : x.IsQueryBound fun _ ↦ q)
    (ρ : SubState A) :
    (compressedRuntime X Y).ForallQueries I
      (fun _ E σ ↦ SupportedIn (Prod.fst ⁻¹' {p : (X × Y) × Database X Y | p.2.size ≤ q - 1} :
        Set (((X × Y) × Database X Y) × E)) σ) x (ρ.prod (compressedRuntime X Y).init).matrix :=
  forallQueries_compressedRuntime I hx (by omega)
    (databaseSupportedOn_kronecker_single_empty (X := X) (Y := Y) ρ.matrix)

end compressed

end Quantum
