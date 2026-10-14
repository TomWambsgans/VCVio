/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.LinearAlgebra.UnitaryGroup
public import VCVio.Quantum.Oracle.Basis

/-!
# The oracle unitary of a function

A quantum algorithm queries a function `H : X → Y` into an additive group `Y` on a register
`X × Y × W`: a query input, a response register and a workspace. The query is the permutation of
the computational basis that adds the value of `H` into the response register,
`|x, y, w⟩ ↦ |x, y + H x, w⟩`. For `Y` a vector space over `ZMod 2` this is the XOR oracle.

## Main definitions

* `Quantum.oracleEquiv H`: the permutation `(x, y, w) ↦ (x, y + H x, w)` of the basis.
* `Quantum.oracleUnitary H`: its permutation matrix. It is unitary
  (`Quantum.oracleUnitary_mem_unitaryGroup`), and `H ↦ oracleUnitary H` turns addition of
  functions into multiplication (`Quantum.oracleUnitary_add`, `Quantum.oracleUnitary_zero`).
* `Quantum.oracleQuery H`: the query as a lossless quantum computation without outcome.
* `Quantum.QuerySupportedOn S ρ`: the operator `ρ` vanishes outside the query inputs in `S`.
  On such operators the query only depends on the restriction of `H` to `S`
  (`Quantum.conj_oracleUnitary_congr`).
-/

public section

open Matrix
open scoped ComplexOrder

namespace Quantum

variable {X Y W : Type*}

/-! ## The basis permutation -/

section oracleEquiv

variable [AddGroup Y]

/-- The permutation of the basis of the register `X × Y × W` that adds `H x` into the response
register: `(x, y, w) ↦ (x, y + H x, w)`. -/
@[expose]
def oracleEquiv (H : X → Y) : X × Y × W ≃ X × Y × W where
  toFun m := (m.1, m.2.1 + H m.1, m.2.2)
  invFun m := (m.1, m.2.1 - H m.1, m.2.2)
  left_inv m := by simp
  right_inv m := by simp

/-- The oracle permutation adds `H x` into the response register. -/
@[simp]
theorem oracleEquiv_apply (H : X → Y) (m : X × Y × W) :
    oracleEquiv H m = (m.1, m.2.1 + H m.1, m.2.2) :=
  rfl

/-- The inverse of the oracle permutation subtracts `H x` from the response register. -/
@[simp]
theorem oracleEquiv_symm_apply (H : X → Y) (m : X × Y × W) :
    (oracleEquiv H).symm m = (m.1, m.2.1 - H m.1, m.2.2) :=
  rfl

/-- The oracle permutation of the zero function is the identity. -/
@[simp]
theorem oracleEquiv_zero : oracleEquiv (0 : X → Y) = Equiv.refl (X × Y × W) :=
  Equiv.ext fun m ↦ by simp

/-- The oracle permutation of a sum applies the oracle permutations one after the other. -/
theorem oracleEquiv_add (H H' : X → Y) :
    oracleEquiv (W := W) (H + H') = (oracleEquiv H).trans (oracleEquiv H') :=
  Equiv.ext fun m ↦ by simp [add_assoc]

/-- The oracle permutation of the negated function is the inverse permutation. -/
theorem oracleEquiv_neg (H : X → Y) : oracleEquiv (W := W) (-H) = (oracleEquiv H).symm :=
  Equiv.ext fun m ↦ by simp [sub_eq_add_neg]

end oracleEquiv

/-! ## The unitary -/

section oracleUnitary

variable [AddCommGroup Y] [DecidableEq X] [DecidableEq Y] [DecidableEq W]

/-- The oracle unitary of `H : X → Y` on the register `X × Y × W`: the permutation matrix sending
the basis vector `|x, y, w⟩` to `|x, y + H x, w⟩`. -/
@[expose]
def oracleUnitary (H : X → Y) : Matrix (X × Y × W) (X × Y × W) ℂ :=
  basisMatrix (oracleEquiv H)

/-- The entry of the oracle unitary at `(m, m')` is one when `m` is `m'` with `H` added into the
response register, and zero otherwise. -/
theorem oracleUnitary_apply (H : X → Y) (m m' : X × Y × W) :
    oracleUnitary H m m' = if m = (m'.1, m'.2.1 + H m'.1, m'.2.2) then 1 else 0 :=
  rfl

/-- The oracle unitary of the zero function is the identity matrix. -/
@[simp]
theorem oracleUnitary_zero : oracleUnitary (0 : X → Y) = (1 : Matrix (X × Y × W) _ ℂ) := by
  rw [oracleUnitary, oracleEquiv_zero]
  exact basisMatrix_id

/-- The adjoint of the oracle unitary of `H` is the oracle unitary of `-H`. -/
theorem conjTranspose_oracleUnitary (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y × W) _ ℂ)ᴴ = oracleUnitary (-H) := by
  rw [oracleUnitary, conjTranspose_basisMatrix_equiv, oracleUnitary, oracleEquiv_neg]

/-- Conjugation by the oracle unitary relabels rows and columns by subtracting `H` from the
response register. -/
theorem conj_oracleUnitary_apply [Fintype X] [Fintype Y] [Fintype W] (H : X → Y)
    (ρ : Matrix (X × Y × W) (X × Y × W) ℂ) (m m' : X × Y × W) :
    MatrixMap.conj (oracleUnitary H) ρ m m' =
      ρ (m.1, m.2.1 - H m.1, m.2.2) (m'.1, m'.2.1 - H m'.1, m'.2.2) := by
  rw [oracleUnitary, conj_basisMatrix_equiv]
  rfl

variable [Fintype X] [Fintype Y] [Fintype W]

/-- The oracle unitary sends the basis vector `|x, y, w⟩` to `|x, y + H x, w⟩`. -/
theorem oracleUnitary_mulVec_single (H : X → Y) (m : X × Y × W) :
    oracleUnitary H *ᵥ Pi.single m 1 = Pi.single (m.1, m.2.1 + H m.1, m.2.2) 1 :=
  basisMatrix_mulVec_single _ m

/-- The oracle unitary of a sum of functions is the product of the oracle unitaries. -/
theorem oracleUnitary_add (H H' : X → Y) :
    (oracleUnitary (H + H') : Matrix (X × Y × W) _ ℂ) = oracleUnitary H * oracleUnitary H' := by
  rw [oracleUnitary, add_comm, oracleEquiv_add, Equiv.coe_trans, basisMatrix_comp]
  rfl

/-- The oracle unitaries of two functions commute. -/
theorem oracleUnitary_mul_comm (H H' : X → Y) :
    (oracleUnitary H : Matrix (X × Y × W) _ ℂ) * oracleUnitary H' =
      oracleUnitary H' * oracleUnitary H := by
  rw [← oracleUnitary_add, ← oracleUnitary_add, add_comm]

/-- The oracle unitary is an isometry. -/
theorem conjTranspose_oracleUnitary_mul_self (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y × W) _ ℂ)ᴴ * oracleUnitary H = 1 :=
  conjTranspose_basisMatrix_mul_self (oracleEquiv H).injective

/-- The oracle unitary is a coisometry. -/
theorem oracleUnitary_mul_conjTranspose_self (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y × W) _ ℂ) * (oracleUnitary H)ᴴ = 1 := by
  rw [conjTranspose_oracleUnitary, ← oracleUnitary_add, add_neg_cancel, oracleUnitary_zero]

/-- The oracle unitary is a unitary matrix. -/
theorem oracleUnitary_mem_unitaryGroup (H : X → Y) :
    (oracleUnitary H : Matrix (X × Y × W) _ ℂ) ∈ Matrix.unitaryGroup (X × Y × W) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (oracleUnitary_mul_conjTranspose_self H)

/-! ## The query as a quantum computation -/

/-- One query to `H` on the register `X × Y × W`: the gate of the oracle unitary. -/
@[expose]
noncomputable def oracleQuery (H : X → Y) : QuantumComp (X × Y × W) Unit :=
  SubInstrument.ofIsometry (oracleUnitary H) (conjTranspose_oracleUnitary_mul_self H)

/-- The unique branch of a query is conjugation by the oracle unitary. -/
@[simp]
theorem branch_oracleQuery_apply (H : X → Y) (u : Unit) :
    (oracleQuery H : QuantumComp (X × Y × W) Unit).branch u = MatrixMap.conj (oracleUnitary H) :=
  SubInstrument.branch_ofIsometry_apply ..

/-- A query is lossless. -/
theorem lossless_oracleQuery (H : X → Y) :
    (oracleQuery H : QuantumComp (X × Y × W) Unit).Lossless :=
  SubInstrument.lossless_ofIsometry _ _

/-- A query to the zero function returns without touching the register. -/
theorem oracleQuery_zero :
    (oracleQuery (0 : X → Y) : QuantumComp (X × Y × W) Unit) = SubInstrument.pure () :=
  SubInstrument.ext <| Finsupp.ext fun u ↦ by simp

/-- A query to `H` followed by a query to `H'` is one query to `H + H'`. -/
theorem oracleQuery_bind_oracleQuery (H H' : X → Y) :
    ((oracleQuery H : QuantumComp (X × Y × W) Unit).bind fun _ ↦ oracleQuery H') =
      oracleQuery (H + H') :=
  SubInstrument.ext <| Finsupp.ext fun u ↦ by
    rw [SubInstrument.branch_bind_unit, branch_oracleQuery_apply, branch_oracleQuery_apply,
      branch_oracleQuery_apply, ← MatrixMap.conj_mul, ← oracleUnitary_add, add_comm]

/-- A query sends the basis state at `(x, y, w)` to the basis state at `(x, y + H x, w)`. -/
theorem post_oracleQuery_basis (H : X → Y) (m : X × Y × W) :
    (oracleQuery H).post (SubState.basis m) () = SubState.basis (m.1, m.2.1 + H m.1, m.2.2) :=
  SubState.ext <| by
    rw [SubInstrument.matrix_post, branch_oracleQuery_apply, SubState.matrix_basis, oracleUnitary,
      conj_basisMatrix_equiv_single]
    rfl

end oracleUnitary

/-! ## Operators supported on a set of query inputs -/

section QuerySupportedOn

/-- The operator `ρ` on the register `X × Y × W` is supported on the query inputs in `S`: an
entry is nonzero only when the query inputs of its row and of its column lie in `S`. For a
normalized state, of trace one, this says that measuring the query register yields an element of
`S` with certainty; for a substate, that the measurement gives zero weight to inputs outside `S`. -/
@[expose]
def QuerySupportedOn (S : Set X) (ρ : Matrix (X × Y × W) (X × Y × W) ℂ) : Prop :=
  ∀ m m', ρ m m' ≠ 0 → m.1 ∈ S ∧ m'.1 ∈ S

/-- Every operator is supported on the set of all query inputs. -/
theorem querySupportedOn_univ (ρ : Matrix (X × Y × W) (X × Y × W) ℂ) :
    QuerySupportedOn Set.univ ρ :=
  fun _ _ _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Support on a set of query inputs passes to larger sets. -/
theorem QuerySupportedOn.mono {S T : Set X} {ρ : Matrix (X × Y × W) (X × Y × W) ℂ}
    (hρ : QuerySupportedOn S ρ) (hST : S ⊆ T) : QuerySupportedOn T ρ :=
  fun m m' h ↦ ⟨hST (hρ m m' h).1, hST (hρ m m' h).2⟩

/-- A basis state is supported on any set containing its query input. -/
theorem querySupportedOn_single [DecidableEq X] [DecidableEq Y] [DecidableEq W] {S : Set X}
    {m : X × Y × W} (hm : m.1 ∈ S) : QuerySupportedOn S (Matrix.single m m (1 : ℂ)) := by
  intro a b h
  rw [Matrix.single_apply] at h
  split_ifs at h with hab
  · exact ⟨hab.1 ▸ hm, hab.2 ▸ hm⟩
  · exact absurd rfl h

variable [AddCommGroup Y] [DecidableEq X] [DecidableEq Y] [DecidableEq W]
  [Fintype X] [Fintype Y] [Fintype W]

/-- On an operator supported on the query inputs in `S`, conjugation by the oracle unitary only
depends on the restriction of the function to `S`. -/
theorem conj_oracleUnitary_congr {S : Set X} {H H' : X → Y} (hH : Set.EqOn H H' S)
    {ρ : Matrix (X × Y × W) (X × Y × W) ℂ} (hρ : QuerySupportedOn S ρ) :
    MatrixMap.conj (oracleUnitary H) ρ = MatrixMap.conj (oracleUnitary H') ρ := by
  ext m m'
  rw [conj_oracleUnitary_apply, conj_oracleUnitary_apply]
  by_cases h : m.1 ∈ S ∧ m'.1 ∈ S
  · rw [hH h.1, hH h.2]
  · have h₁ := of_not_not fun h₀ ↦
      h (hρ (m.1, m.2.1 - H m.1, m.2.2) (m'.1, m'.2.1 - H m'.1, m'.2.2) h₀)
    have h₂ := of_not_not fun h₀ ↦
      h (hρ (m.1, m.2.1 - H' m.1, m.2.2) (m'.1, m'.2.1 - H' m'.1, m'.2.2) h₀)
    exact h₁.trans h₂.symm

/-- A query keeps an operator supported on the query inputs in `S`. -/
theorem QuerySupportedOn.conj_oracleUnitary {S : Set X} {ρ : Matrix (X × Y × W) (X × Y × W) ℂ}
    (hρ : QuerySupportedOn S ρ) (H : X → Y) :
    QuerySupportedOn S (MatrixMap.conj (oracleUnitary H) ρ) := fun m m' h ↦ by
  rw [conj_oracleUnitary_apply] at h
  exact hρ (m.1, m.2.1 - H m.1, m.2.2) (m'.1, m'.2.1 - H m'.1, m'.2.2) h

/-- On a substate supported on the query inputs in `S`, a query only depends on the restriction
of the function to `S`. -/
theorem post_oracleQuery_congr {S : Set X} {H H' : X → Y} (hH : Set.EqOn H H' S)
    {ρ : SubState (X × Y × W)} (hρ : QuerySupportedOn S ρ.matrix) :
    (oracleQuery H).post ρ () = (oracleQuery H').post ρ () :=
  SubState.ext <| by
    rw [SubInstrument.matrix_post, SubInstrument.matrix_post, branch_oracleQuery_apply,
      branch_oracleQuery_apply, conj_oracleUnitary_congr hH hρ]

end QuerySupportedOn

end Quantum
