/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Combinators
public import VCVio.Quantum.Comp.QueryMass
public import VCVio.Quantum.Oracle.Basis

/-!
# Emulated oracles

An *emulated oracle* (ePrint 2025/2166, §4.1, l.1328–1343) is a pair `EO = (Init, (U_i)_i)`: a
private register `S` prepared by `Init`, and for each port `i` a unitary `U_i` on the port's
register `X_i` and `S`. The adversary queries it with a coherent index: a query on the registers
`(I, X)` applies `U = ∑ᵢ |i⟩⟨i|_I ⊗ (U_i)_{X_i S}` (l.1339–1342).

`Quantum.EmulatedOracle P In` records the unitaries. Everything else is derived from them:

* `Quantum.EmulatedOracle.toRuntime`: the runtime over the signature of unitary ports
  `Quantum.uSpec P In`, one classical port per unitary; each step is the gate of `U_i`.
* `Quantum.EmulatedOracle.coherent`: the emulated oracle with one port, whose register
  `Σ i, In i` carries the index, and whose unitary is the block-diagonal `∑ᵢ |i⟩⟨i| ⊗ U_i`. This
  is the paper's query interface, and the definitions of security quantify over programs run
  against `E.coherent.toRuntime`.
* `Quantum.EmulatedOracle.extend` and `Quantum.EmulatedOracle.addRegister`: further unitary ports
  on the same private register, and an untouched register beside it. They agree with the general
  runtime combinators `Quantum.QuantumRuntime.extend` and `Quantum.QuantumRuntime.addRegister`.

## Masses

The query mass `mass(A, i, j)` of Definition 4.1 (l.1359–1365) is `‖P_mass^(i) |ψ_j⟩‖²`, with
`P_mass^(i)` the projector of the index register onto `i` and `|ψ_j⟩` the joint state before the
`j`-th query; the total mass `TotalMass(A, i)` of Definition 4.3 (l.1382–1386) sums it over the
queries. `Quantum.EmulatedOracle.totalMass` is the case of a general program and a general
(mixed, subnormalised) state: the summed trace of the index-`i` component of the input of each
call to the coherent port, a query weight in the sense of `VCVio.Quantum.Comp.QueryMass`.

## Main statements

* `Quantum.EmulatedOracle.toRuntime_step_branch`: each step is the Kraus map of its unitary, the
  form used by the square-root hybrid (`VCVio.Quantum.Comp.Hybrid`).
* `Quantum.EmulatedOracle.toRuntime_addRegister`: the two ways of adjoining a register agree.
* `Quantum.EmulatedOracle.sum_totalMass` (Remark 4.2, l.1370–1373): the masses on the indices
  add up to the query mass of the coherent port, which a `t`-query program bounds by `t` times
  the trace of the initial state (`Quantum.EmulatedOracle.sum_totalMass_le`).
* `Quantum.EmulatedOracle.totalMass_bind`: masses add under sequencing, from the general
  `Quantum.QuantumRuntime.totalWeight_bind`.

## Classical-port programs

A program over `Quantum.uSpec P In`, which names the port of each call classically, is a special
coherent program: `Quantum.QuantumComp.toCoherent` embeds the input of each call of port `i` into
the summand `i` of the coherent register, calls the coherent port, and reads the summand back.

* `Quantum.EmulatedOracle.run_toCoherent`: the translation runs as the original program.
* `Quantum.EmulatedOracle.totalMass_toCoherent`: its mass on `i` is the query mass of port `i`.
* `Quantum.QuantumComp.isQueryBound_toCoherent`: a budget `b` becomes the budget `∑ i, b i`.

Every statement about programs against `E.coherent.toRuntime` therefore specialises to
classical-port programs against `E.toRuntime`, with per-port query masses in place of total
masses.

## Implementation notes

The paper's index register is `I ⊗ X_1 ⊗ … ⊗ X_k` with `U_i` acting on `X_i`; ours is the direct
sum `Σ i, In i`. The basis injection `|i, x_1 … x_k⟩ ↦ |i, x_i⟩ ⊗ |x_1 … 0 … x_k⟩` intertwines the
two oracles, and an adversary can apply it before each query and undo it after, so the two
adversary classes have the same laws and the same masses.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v u₁ v₁ uL vL w w₁

namespace Quantum

/-! ## Summed query weights -/

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{uL, vL}}
  (I : L.Interp) {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}

/-- The weight `w` summed over all calls of `x` run against `R` from `ρ`. The total query mass
`Quantum.QuantumRuntime.queryMass` is the case of the trace on one port. -/
@[expose]
noncomputable def totalWeight (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) : ℝ≥0∞ :=
  ∑' j, R.queryWeight I w x ρ j

variable {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- A program that stops at once has no weight. -/
@[simp]
theorem totalWeight_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I w (QuantumComp.pure (L := L) (spec := spec) y) ρ = 0 := by
  simp [totalWeight]

/-- The weight of a local operation followed by a continuation is the weight of the
continuations, from the branches of the operation. -/
theorem totalWeight_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I w (QuantumComp.primBind o k) ρ =
      ∑' b, R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ) := by
  simp only [totalWeight, queryWeight_primBind]
  exact ENNReal.tsum_comm

/-- A call followed by a continuation adds the weight of the call's input to the weight of the
continuations. -/
theorem totalWeight_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I w (QuantumComp.queryBind i E ℓ k) ρ =
      w i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) := by
  rw [totalWeight, tsum_eq_zero_add' ENNReal.summable, queryWeight_queryBind_zero]
  simp only [queryWeight_queryBind_succ, totalWeight]
  rw [ENNReal.tsum_comm]

open Classical in
/-- The total query mass is the summed weight of the trace on one port. -/
theorem queryMass_eq_totalWeight (x : QuantumComp L spec X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) :
    R.queryMass I x ρ i =
      R.totalWeight I (fun i' σ ↦ if i' = i then ENNReal.ofReal σ.trace.re else 0) x ρ :=
  rfl

section cp

variable {K : spec.Port → Type*} [∀ i, Fintype (K i)] {Φ : ∀ i, MatrixMap (spec.In i × R.D) (K i)}

/-- A weight given by the trace of a completely positive map is countably additive on summable
families of positive semidefinite operators. -/
theorem ofReal_trace_re_tsum_of_isCP (hΦ : ∀ i, (Φ i).IsCP) {ι : Type*} (i : spec.Port)
    (g : ι → Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ) (hg : Summable g)
    (hpos : ∀ b, (g b).PosSemidef) :
    ENNReal.ofReal (Φ i (∑' b, g b)).trace.re = ∑' b, ENNReal.ofReal (Φ i (g b)).trace.re := by
  rw [MatrixMap.map_tsum _ hg]
  exact ofReal_trace_re_tsum (MatrixMap.summable_comp _ hg) fun b ↦ (hΦ i).posSemidef (hpos b)

/-- On positive semidefinite inputs, the summed weight of the trace of completely positive maps
is countably additive in the state. -/
theorem totalWeight_tsum_state (hΦ : ∀ i, (Φ i).IsCP) (x : QuantumComp L spec X A) {ι : Type*}
    {f : ι → Matrix (A × R.D) (A × R.D) ℂ} (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) :
    R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x (∑' b, f b) =
      ∑' b, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x (f b) := by
  refine (tsum_congr fun j ↦ R.queryWeight_tsum_state I
    (w := fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re)
    (fun i g hg hgpos ↦ R.ofReal_trace_re_tsum_of_isCP hΦ i g hg hgpos) x hf hpos j).trans ?_
  exact ENNReal.tsum_comm

/-- **Summed weights add under sequencing.** For a weight given by the trace of completely
positive maps, the summed weight of `x.bind k` is the summed weight of `x` plus, for every leaf
`p` of `x`, the summed weight of the continuation `k p.1 p.2` from the branch of the run of `x`
at `p`. This is the general form of `Quantum.QuantumRuntime.queryMass_bind`. -/
theorem totalWeight_bind (hΦ : ∀ i, (Φ i).IsCP) (x : QuantumComp L spec X A)
    (k : ∀ u, X u → QuantumComp L spec Y u) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (x.bind k) ρ =
      R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x ρ +
        ∑' p, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k p.1 p.2)
          ((R.run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [QuantumComp.pure_bind, totalWeight_pure, zero_add, run_pure,
      tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, totalWeight,
          ENNReal.tsum_eq_zero]
        exact fun j ↦ R.queryWeight_zero I (fun i ↦ by simp) _ j,
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
  | primBind _ o k' ih =>
    have hb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    rw [QuantumComp.primBind_bind, totalWeight_primBind, totalWeight_primBind, run_primBind]
    simp only [fun b ↦ ih b (hb b), DSubInstrument.branch_bind_apply]
    rw [ENNReal.tsum_add]
    congr 1
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun p ↦ (R.totalWeight_tsum_state I hΦ _
      ((((I o).frame R.D).isCPTNIFamily.comp_eval
        (fun b ↦ (R.run I (k' b)).isCPTNIFamily) p).summable_apply ρ)
      (fun b ↦ (R.run I (k' b)).posSemidef_branch_apply p (hb b))).symm
  | queryBind _ i' E ℓ k' ih =>
    have hb := fun r ↦ (R.queryStep i' E ℓ).posSemidef_branch_apply r hρ
    have hrun : ∀ p, (R.run I (QuantumComp.queryBind i' E ℓ k')).branch p ρ =
        ∑' r, (R.run I (k' r)).branch p ((R.queryStep i' E ℓ).branch r ρ) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      rfl
    have htail : ∑' p, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k p.1 p.2)
          ((R.run I (QuantumComp.queryBind i' E ℓ k')).branch p ρ) =
        ∑' r, ∑' p, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k p.1 p.2)
          ((R.run I (k' r)).branch p ((R.queryStep i' E ℓ).branch r ρ)) := by
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun p ↦ ?_
      rw [hrun p]
      exact R.totalWeight_tsum_state I hΦ _
        (((SubInstrument.toD (R.queryStep i' E ℓ)).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k' r)).isCPTNIFamily) p).summable_apply ρ)
        (fun r ↦ (R.run I (k' r)).posSemidef_branch_apply p (hb r))
    rw [QuantumComp.queryBind_bind, htail, totalWeight_queryBind, totalWeight_queryBind, add_assoc,
      ← ENNReal.tsum_add]
    simp only [fun r ↦ ih r (hb r)]

end cp

end QuantumRuntime

/-! ## Emulated oracles -/

/-- **Emulated oracle** (ePrint 2025/2166, §4.1, l.1328–1343): a private register `S` with an
initial substate `init`, and for each port `i` a unitary `U i` on the port's register `In i` and
`S`. -/
structure EmulatedOracle (P : Type u) (In : P → QReg) where
  /-- The private register of the oracle (the paper's `S`). -/
  S : QReg
  /-- The initial substate of the private register (the output of the paper's `Init`). -/
  init : SubState S
  /-- The unitary of port `i` on `In i × S` (the paper's `U_i`). -/
  U : ∀ i, Matrix (In i × S) (In i × S) ℂ
  /-- Each `U i` is unitary. -/
  unitary : ∀ i, U i ∈ Matrix.unitaryGroup (In i × S) ℂ

/-- A matrix moved along a bijection of its basis stays unitary. -/
theorem reindex_mem_unitaryGroup {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) {M : Matrix m m ℂ} (hM : M ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hM ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hM,
    Matrix.submatrix_one_equiv]

/-- A block-diagonal matrix of unitaries is unitary. -/
theorem blockDiagonal'_mem_unitaryGroup {o : Type*} [Fintype o] [DecidableEq o]
    {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {M : ∀ i, Matrix (m i) (m i) ℂ}
    (hM : ∀ i, M i ∈ Matrix.unitaryGroup (m i) ℂ) :
    Matrix.blockDiagonal' M ∈ Matrix.unitaryGroup (Σ i, m i) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.star_eq_conjTranspose, fun i ↦ Matrix.mem_unitaryGroup_iff'.mp (hM i)]
  exact Matrix.blockDiagonal'_one

/-- The Kraus map of a matrix moved along a bijection of its basis moves the input back, applies
the Kraus map of the matrix, and moves the result forward. -/
theorem MatrixMap.conj_reindex_apply {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n)
    (M : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    MatrixMap.conj (Matrix.reindex e e M) ρ =
      (M * ρ.submatrix e e * Mᴴ).submatrix e.symm e.symm := by
  rw [MatrixMap.conj_apply, Matrix.conjTranspose_reindex, Matrix.reindex_apply,
    Matrix.reindex_apply]
  have h : ρ = (ρ.submatrix e e).submatrix e.symm e.symm := by simp
  conv_lhs => rw [h]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- The Kraus map of `U ⊗ 1`, regrouped along `Equiv.prodAssoc`, in the form of the steps of
`Quantum.QuantumRuntime.addRegister`. -/
private theorem conj_reindex_prodAssoc_kronecker_one {a s g : Type*} [Fintype a] [Fintype s]
    [Fintype g] [DecidableEq g] (U : Matrix (a × s) (a × s) ℂ)
    (ρ : Matrix (a × s × g) (a × s × g) ℂ) :
    MatrixMap.conj (Matrix.reindex (Equiv.prodAssoc a s g) (Equiv.prodAssoc a s g)
      (U ⊗ₖ (1 : Matrix g g ℂ))) ρ =
      ((MatrixMap.conj U).amplify g (ρ.submatrix (Equiv.prodAssoc a s g)
        (Equiv.prodAssoc a s g))).submatrix (Equiv.prodAssoc a s g).symm
        (Equiv.prodAssoc a s g).symm := by
  rw [MatrixMap.amplify_conj, MatrixMap.conj_apply]
  exact MatrixMap.conj_reindex_apply _ _ ρ

namespace EmulatedOracle

variable {P : Type u} {In : P → QReg} (E : EmulatedOracle P In)

/-- The unitaries of an emulated oracle are isometries. -/
theorem conjTranspose_mul_self (i : P) : (E.U i)ᴴ * E.U i = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (E.unitary i)

/-- **The runtime of an emulated oracle**, one classical port per unitary: the private register
`S` starts in `init`, and a call of port `i` applies the gate of `U i`
(`Quantum.SubInstrument.ofIsometry`). -/
@[expose, reducible]
noncomputable def toRuntime : QuantumRuntime (uSpec P In) where
  D := E.S
  init := E.init
  step i := SubInstrument.ofIsometry (E.U i) (E.conjTranspose_mul_self i)

/-- The private register of the runtime is the private register of the oracle. -/
theorem toRuntime_D : E.toRuntime.D = E.S :=
  rfl

/-- The runtime starts in the initial substate of the oracle. -/
theorem toRuntime_init : E.toRuntime.init = E.init :=
  rfl

/-- **Each step is the Kraus map of its unitary.** This is the form of the steps assumed by the
square-root hybrid (`VCVio.Quantum.Comp.Hybrid`), so Lemma 5.7 of ePrint 2025/2166 applies to
emulated oracles. -/
theorem toRuntime_step_branch (i : P) (r : Unit) :
    (E.toRuntime.step i).branch r = MatrixMap.conj (E.U i) :=
  rfl

/-- The steps of the runtime of an emulated oracle are lossless. -/
theorem lossless_toRuntime_step (i : P) : (E.toRuntime.step i).Lossless :=
  SubInstrument.lossless_ofIsometry _ (E.conjTranspose_mul_self i)

/-! ### Extension by further ports -/

/-- Add unitary ports `U' j` on the same private register (the step from `EO` to `EO^(Ext)` of
ePrint 2025/2166, l.2846–2847). -/
@[expose]
def extend {P' : Type u} {In' : P' → QReg} (U' : ∀ j, Matrix (In' j × E.S) (In' j × E.S) ℂ)
    (hU' : ∀ j, U' j ∈ Matrix.unitaryGroup (In' j × E.S) ℂ) :
    EmulatedOracle (P ⊕ P') (Sum.elim In In') where
  S := E.S
  init := E.init
  U
    | .inl i => E.U i
    | .inr j => U' j
  unitary
    | .inl i => E.unitary i
    | .inr j => hU' j

section extend

variable {P' : Type u} {In' : P' → QReg} (U' : ∀ j, Matrix (In' j × E.S) (In' j × E.S) ℂ)
  (hU' : ∀ j, U' j ∈ Matrix.unitaryGroup (In' j × E.S) ℂ)

/-- The old ports of an extended oracle are answered as before. Port-wise agreement with
`Quantum.QuantumRuntime.extend`: `uSpec (P ⊕ P') _` and `(uSpec P In).sum (uSpec P' In')` differ
in the form of their result types, which are equal but not definitionally, so the agreement is
stated per port. -/
theorem toRuntime_extend_step_inl (i : P) :
    (E.extend U' hU').toRuntime.step (.inl i) = E.toRuntime.step i :=
  rfl

/-- The new ports of an extended oracle are answered by the gates of the added unitaries. -/
theorem toRuntime_extend_step_inr (j : P') :
    (E.extend U' hU').toRuntime.step (.inr j) =
      SubInstrument.ofIsometry (U' j) (Matrix.mem_unitaryGroup_iff'.mp (hU' j)) :=
  rfl

end extend

/-! ### An untouched register -/

/-- Adjoin a register `G` in the substate `σ` beside the private register; the ports act as
`U i ⊗ 1_G` (the step from `Init` to `Init′` of ePrint 2025/2166, l.2918). -/
@[expose]
noncomputable def addRegister (G : QReg) (σ : SubState G) : EmulatedOracle P In where
  S := QReg.of (E.S × G)
  init := E.init.prod σ
  U i := Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
    (E.U i ⊗ₖ (1 : Matrix G G ℂ))
  unitary i := reindex_mem_unitaryGroup _
    (Matrix.kronecker_mem_unitary (E.unitary i) (one_mem _))

/-- **The two ways of adjoining a register agree**: the runtime of `E.addRegister G σ` is the
runtime of `E` with the register `G` added by `Quantum.QuantumRuntime.addRegister`. -/
theorem toRuntime_addRegister (G : QReg) (σ : SubState G) :
    (E.addRegister G σ).toRuntime = E.toRuntime.addRegister G σ := by
  refine congrArg (QuantumRuntime.mk _ _) (funext fun i ↦ SubInstrument.ext <| funext fun r ↦
    LinearMap.ext fun ρ ↦ ?_)
  exact (conj_reindex_prodAssoc_kronecker_one (E.U i) ρ).trans
    (QuantumRuntime.addRegister_step_branch_apply E.toRuntime G σ i r ρ).symm

/-! ### The coherent index -/

section coherent

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} (E : EmulatedOracle P In)

/-- The coherent query register `Σ i, In i`: the index together with the register of the indexed
port. It is the direct-sum form of the paper's `I ⊗ X_1 ⊗ … ⊗ X_k` (see the module docstring). -/
@[expose, reducible]
def cohIn (In : P → QReg) : QReg :=
  QReg.of (Σ i, In i)

/-- The signature of the coherent index: one unitary port on `cohIn In`. -/
@[expose, reducible]
def cohSpec (In : P → QReg) : QuantumOracleSpec.{0, 0} :=
  uSpec Unit fun _ ↦ cohIn In

/-- **The coherent oracle** (ePrint 2025/2166, l.1339–1342): one port on the coherent register,
answered by `U = ∑ᵢ |i⟩⟨i| ⊗ U_i`, the block-diagonal matrix of the unitaries. -/
@[expose, reducible]
noncomputable def coherent : EmulatedOracle Unit fun _ ↦ cohIn In where
  S := E.S
  init := E.init
  U _ := Matrix.reindex (Equiv.sigmaProdDistrib _ _).symm (Equiv.sigmaProdDistrib _ _).symm
    (Matrix.blockDiagonal' E.U)
  unitary _ := reindex_mem_unitaryGroup _
    (blockDiagonal'_mem_unitaryGroup E.unitary)

/-- The projector of the coherent register onto the index `i`, tensored with the identity on the
private register (the paper's `P_mass^(i) = |i⟩⟨i|_I`, l.1364). -/
@[expose]
noncomputable def indexProj (i : P) : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ :=
  Matrix.diagonal fun a ↦ if a.1.1 = i then 1 else 0

/-- The weight of the index-`i` component of an operator: the trace of its compression by the
projector onto `i`, the squared norm `‖P_mass^(i) |ψ⟩‖²` for a pure state. -/
theorem trace_conj_indexProj (i : P) (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) :
    (MatrixMap.conj (E.indexProj i) σ).trace = ∑ a, if a.1.1 = i then σ a a else 0 := by
  simp only [MatrixMap.conj_apply, indexProj, Matrix.diagonal_conjTranspose, Matrix.trace,
    Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : a.1.1 = i <;> simp [h]

/-- The weights of the index components add up to the trace. -/
theorem sum_trace_conj_indexProj (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) :
    ∑ i, (MatrixMap.conj (E.indexProj i) σ).trace = σ.trace := by
  calc ∑ i, (MatrixMap.conj (E.indexProj i) σ).trace
      = ∑ i, ∑ a, if a.1.1 = i then σ a a else 0 :=
        Finset.sum_congr rfl fun i _ ↦ E.trace_conj_indexProj i σ
    _ = ∑ a, ∑ i, if a.1.1 = i then σ a a else 0 := Finset.sum_comm
    _ = σ.trace := Finset.sum_congr rfl fun a _ ↦ by simp

/-- **Total query mass** (ePrint 2025/2166, Definitions 4.1 and 4.3, l.1359–1386): the weight of
the index-`i` component of the input of every call of `x` to the coherent oracle, summed over
the calls, for `x` run from the joint operator `ρ` on `A × S`. -/
@[expose]
noncomputable def totalMass {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {A : QReg} (x : QuantumComp L (cohSpec In) W A) (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    ℝ≥0∞ :=
  ∑' j, E.coherent.toRuntime.queryWeight I
    (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re) x ρ j

variable {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}

/-- **Remark 4.2** (l.1370–1373): on a positive semidefinite input, the masses on the indices add
up to the query mass of the coherent port. -/
theorem sum_totalMass (x : QuantumComp L (cohSpec In) W A) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) :
    ∑ i, E.totalMass I x ρ i = E.coherent.toRuntime.queryMass I x ρ () := by
  rw [QuantumRuntime.queryMass_eq_totalWeight]
  simp only [totalMass, QuantumRuntime.totalWeight]
  rw [← tsum_fintype (L := .unconditional P), ENNReal.tsum_comm]
  refine tsum_congr fun j ↦ ?_
  refine (E.coherent.toRuntime.tsum_queryWeight I _ x ρ j).trans ?_
  have h : ∀ σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ, σ.PosSemidef →
      ∑' i, ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re =
        ENNReal.ofReal σ.trace.re := fun σ hσ ↦ by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦
      ((MatrixMap.isCP_conj _).posSemidef hσ).trace_re_nonneg, ← Complex.re_sum,
      sum_trace_conj_indexProj]
  exact le_antisymm
    (E.coherent.toRuntime.queryWeight_mono I (fun i' σ hσ ↦ by
      simp only [↓reduceIte]
      exact (h σ hσ).le) x hρ j)
    (E.coherent.toRuntime.queryWeight_mono I (fun i' σ hσ ↦ by
      simp only [↓reduceIte]
      exact (h σ hσ).ge) x hρ j)

/-- The mass on one index is at most the query mass of the coherent port. -/
theorem totalMass_le_queryMass (x : QuantumComp L (cohSpec In) W A)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) (i : P) :
    E.totalMass I x ρ i ≤ E.coherent.toRuntime.queryMass I x ρ () := by
  rw [← E.sum_totalMass I x hρ]
  exact Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i)

/-- **Masses and query budgets.** A program making at most `t` queries has masses on the indices
adding up to at most `t` times the trace of the initial state. -/
theorem sum_totalMass_le {x : QuantumComp L (cohSpec In) W A} {t : ℕ}
    (hx : x.IsQueryBoundAt () t) {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, E.totalMass I x ρ i ≤ t * ENNReal.ofReal ρ.trace.re := by
  rw [E.sum_totalMass I x hρ]
  exact E.coherent.toRuntime.queryMass_le_of_isQueryBoundAt I hx hρ

/-- **Masses add under sequencing.** The mass of `x.bind k` on `i` is the mass of `x` plus, for
every leaf `p` of `x`, the mass of the continuation from the branch of the run of `x` at `p`. -/
theorem totalMass_bind {Y : QReg → Type w₁} (x : QuantumComp L (cohSpec In) W A)
    (k : ∀ u, W u → QuantumComp L (cohSpec In) Y u) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) (i : P) :
    E.totalMass I (x.bind k) ρ i =
      E.totalMass I x ρ i +
        ∑' p, E.totalMass I (k p.1 p.2) ((E.coherent.toRuntime.run I x).branch p ρ) i :=
  E.coherent.toRuntime.totalWeight_bind I (Φ := fun _ ↦ MatrixMap.conj (E.indexProj i))
    (fun _ ↦ MatrixMap.isCP_conj _) x k hρ

end coherent

end EmulatedOracle

/-! ## Matrix helpers for the coherent bridge -/

section matrixHelpers

variable {l m n o : Type*}

/-- Compressing by basis matrices picks out a submatrix. -/
theorem conjTranspose_basisMatrix_mul_mul_basisMatrix [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (f : l → m) (g : o → n) (M : Matrix m n ℂ) :
    (basisMatrix f)ᴴ * M * basisMatrix g = M.submatrix f g := by
  ext a b
  simp [Matrix.mul_apply, apply_ite (star : ℂ → ℂ), ite_mul, mul_ite, Finset.sum_ite_eq']

/-- The basis matrix of a bijection is the adjoint of the basis matrix of its inverse. -/
theorem basisMatrix_equiv_eq_conjTranspose [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    basisMatrix e = (basisMatrix e.symm)ᴴ := by
  rw [conjTranspose_basisMatrix_equiv, Equiv.symm_symm]

/-- A basis matrix beside an identity is the basis matrix of the product map. -/
theorem basisMatrix_kronecker_one [DecidableEq m] [DecidableEq n] (f : l → m) :
    basisMatrix f ⊗ₖ (1 : Matrix n n ℂ) = basisMatrix (Prod.map f id) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases h1 : a = f b <;> by_cases h2 : c = d <;> simp [h1, h2]

/-- If `K * Kᴴ = 1`, then `Kᴴ * K` is a projector, so `1 - Kᴴ * K` is positive semidefinite. -/
theorem posSemidef_one_sub_conjTranspose_mul_self [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n]
    {K : Matrix m n ℂ} (hK : K * Kᴴ = 1) : (1 - Kᴴ * K).PosSemidef := by
  have hQ : Kᴴ * K * (Kᴴ * K) = Kᴴ * K := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc K, hK, Matrix.one_mul]
  have h : (1 - Kᴴ * K)ᴴ * (1 - Kᴴ * K) = 1 - Kᴴ * K := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hQ, sub_self, sub_zero]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end matrixHelpers

/-- A call whose step is a Kraus map is the Kraus map of the regrouped step beside the identity
on the remainder. -/
theorem QuantumRuntime.queryStep_branch_eq_conj {spec : QuantumOracleSpec.{u₁, v₁}}
    (R : QuantumRuntime spec) {i : spec.Port} {r : spec.Result i}
    {M : Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ}
    (hM : (R.step i).branch r = MatrixMap.conj M) (F : QReg) {A : QReg}
    (ℓ : A ≃ spec.In i × F) :
    (R.queryStep i F ℓ).branch r =
      MatrixMap.conj (basisMatrix (QuantumRuntime.queryEquivOut (spec.Out i) R.D F) *
        (M ⊗ₖ (1 : Matrix F F ℂ)) * basisMatrix (QuantumRuntime.queryEquivIn ℓ R.D)) := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [QuantumRuntime.queryStep_branch_apply, SubInstrument.branch_frame_apply, hM,
    MatrixMap.amplify_conj, SubInstrument.branch_relabel, SubInstrument.branch_relabel,
    MatrixMap.conj_mul, MatrixMap.conj_mul]
  rfl

/-! ## Classical-port programs as coherent programs -/

namespace EmulatedOracle

section bridge

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}

/-- The injection of the register of port `i`, beside a remainder `F`, into the coherent
register beside `F`: the basis vector `|x, f⟩` goes to `|⟨i, x⟩, f⟩`. -/
@[expose]
def cohInj (i : P) (F : Type*) : In i × F → cohIn In × F :=
  fun p ↦ (⟨i, p.1⟩, p.2)

/-- The injection of summand `i` is injective. -/
theorem cohInj_injective (i : P) (F : Type*) : Function.Injective (cohInj (In := In) i F) := by
  rintro ⟨y, f⟩ ⟨y', f'⟩ h
  simp only [cohInj, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  rw [h.1, h.2]

/-- Before a call of port `i` made through the coherent port: the isometry that moves the input
`In i`, exposed by `ℓ`, into the summand `i` of the coherent register. -/
@[expose]
noncomputable def cohEmbed (i : P) (F : QReg) {A : QReg} (ℓ : A ≃ In i × F) :
    SubInstrument A (cohIn In × F) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (basisMatrix (cohInj i F ∘ ℓ))) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (by
      rw [conjTranspose_basisMatrix_mul_self ((cohInj_injective i F).comp ℓ.injective), sub_self]
      exact Matrix.PosSemidef.zero))

/-- After a call of port `i` made through the coherent port: the contraction that reads the
summand `i` of the coherent register back into `In i`. -/
@[expose]
noncomputable def cohProject (i : P) (F : QReg) :
    SubInstrument (cohIn In × F) (In i × F) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (basisMatrix (cohInj (In := In) i F))ᴴ)
    (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_mul_self (by
      rw [Matrix.conjTranspose_conjTranspose,
        conjTranspose_basisMatrix_mul_self (cohInj_injective i F)])))

end bridge

end EmulatedOracle

namespace QuantumComp

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} {W : QReg → Type w}

open EmulatedOracle in
/-- Recursion for `Quantum.QuantumComp.toCoherent` on the underlying trees. -/
@[expose]
noncomputable def toCoherentAux : {A : QReg} →
    IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{v} (uSpec P In)) W A →
      QuantumComp LocalSig.instruments.{v} (cohSpec In) W A
  | _, .pure y => QuantumComp.pure y
  | _, .liftBind (.prim o) k => QuantumComp.primBind o fun b ↦ toCoherentAux (k (ULift.up b))
  | _, .liftBind (.query i F ℓ) k =>
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of (cohIn In × F), SubInstrument.toD (cohEmbed i F ℓ)⟩ fun _ ↦
        QuantumComp.queryBind (A := QReg.of (cohIn In × F)) () F (Equiv.refl _) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of (In i × F), SubInstrument.toD (cohProject i F)⟩ fun _ ↦
            toCoherentAux (k (ULift.up ()))

open EmulatedOracle in
/-- **Classical-port programs as coherent programs** (design §2.5). A call of port `i` on
`In i × F` becomes a call of the coherent port on `cohIn In × F`: before it, the isometry
`Quantum.EmulatedOracle.cohEmbed` moves the input into the summand `i`; after it, the contraction
`Quantum.EmulatedOracle.cohProject` reads it back. No weight is lost, since the coherent unitary
preserves the summand `i` (`Quantum.EmulatedOracle.run_toCoherent`). The contraction is not
trace preserving on the whole coherent register, so `toCoherent` is not syntactically lossless,
even though its runs are those of the original program. -/
@[expose]
noncomputable def toCoherent {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A) :
    QuantumComp LocalSig.instruments.{v} (cohSpec In) W A :=
  toCoherentAux x

/-- A leaf is translated to itself. -/
@[simp]
theorem toCoherent_pure {A : QReg} (y : W A) :
    (QuantumComp.pure (L := LocalSig.instruments.{v}) (spec := uSpec P In) y).toCoherent =
      QuantumComp.pure y :=
  rfl

/-- Local operations are kept. -/
@[simp]
theorem toCoherent_primBind {A : QReg} (o : LocalSig.instruments.{v}.Op A)
    (k : (b : LocalSig.instruments.{v}.Outcome o) →
      QuantumComp LocalSig.instruments.{v} (uSpec P In) W (LocalSig.instruments.{v}.next o b)) :
    (QuantumComp.primBind o k).toCoherent = QuantumComp.primBind o fun b ↦ (k b).toCoherent :=
  rfl

open EmulatedOracle in
/-- A call of port `i` becomes an embedding, a call of the coherent port and a projection. -/
theorem toCoherent_queryBind {A : QReg} (i : P) (F : QReg) (ℓ : A ≃ In i × F)
    (k : Unit → QuantumComp LocalSig.instruments.{v} (uSpec P In) W (QReg.of (In i × F))) :
    (QuantumComp.queryBind (spec := uSpec P In) i F ℓ k).toCoherent =
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of (cohIn In × F), SubInstrument.toD (cohEmbed i F ℓ)⟩ fun _ ↦
        QuantumComp.queryBind (A := QReg.of (cohIn In × F)) () F (Equiv.refl _) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of (In i × F), SubInstrument.toD (cohProject i F)⟩ fun _ ↦
            (k ()).toCoherent :=
  rfl

/-- **Budgets of the coherent translation.** A program within the budget `b` makes, through the
coherent port, at most the total budget `∑ i, b i` of calls. -/
theorem isQueryBound_toCoherent {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A} {b : P → ℕ}
    (hx : x.IsQueryBound b) : x.toCoherent.IsQueryBound fun _ ↦ ∑ i, b i := by
  induction x using QuantumComp.inductionOn generalizing b with
  | pure _ _ => exact isQueryBound_pure _ _
  | primBind _ o k ih =>
    rw [toCoherent_primBind, isQueryBound_primBind_iff]
    exact fun c ↦ ih c ((isQueryBound_primBind_iff o k b).mp hx c)
  | queryBind _ i F ℓ k ih =>
    obtain ⟨hpos, hk⟩ := (isQueryBound_queryBind_iff i F ℓ k b).mp hx
    rw [toCoherent_queryBind, isQueryBound_primBind_iff]
    intro _
    rw [isQueryBound_queryBind_iff]
    refine ⟨Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i, Finset.mem_univ i, hpos⟩, fun _ ↦ ?_⟩
    rw [isQueryBound_primBind_iff]
    intro _
    have hsum : ∑ j, Function.update b i (b i - 1) j = ∑ j, b j - 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
        (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
      omega
    have h := ih () (hk ())
    convert h using 1
    funext u
    rw [Function.update_self, hsum]

end QuantumComp

namespace EmulatedOracle

section bridge

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} (E : EmulatedOracle P In)
  {W : QReg → Type w}

/-- The matrix identity behind the coherent translation: compressing the coherent call, regrouped
for a call on `cohIn In × F`, by the basis injection of summand `i` gives the call of port `i`. -/
theorem cohCall_matrix (i : P) (F : QReg) {A : QReg} (ℓ : A ≃ In i × F) :
    ((basisMatrix (cohInj (In := In) i F))ᴴ ⊗ₖ (1 : Matrix E.S E.S ℂ)) *
        (basisMatrix (QuantumRuntime.queryEquivOut (cohIn In) E.S F) *
          (E.coherent.U () ⊗ₖ (1 : Matrix F F ℂ)) *
          basisMatrix (QuantumRuntime.queryEquivIn (Equiv.refl (cohIn In × F)) E.S)) *
        (basisMatrix (cohInj i F ∘ ℓ) ⊗ₖ (1 : Matrix E.S E.S ℂ)) =
      basisMatrix (QuantumRuntime.queryEquivOut (In i) E.S F) * (E.U i ⊗ₖ (1 : Matrix F F ℂ)) *
        basisMatrix (QuantumRuntime.queryEquivIn ℓ E.S) := by
  rw [← Matrix.conjTranspose_one, ← Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    basisMatrix_kronecker_one, basisMatrix_kronecker_one,
    basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut (cohIn In) E.S F),
    basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut (In i) E.S F),
    conjTranspose_basisMatrix_mul_mul_basisMatrix, conjTranspose_basisMatrix_mul_mul_basisMatrix,
    conjTranspose_basisMatrix_mul_mul_basisMatrix]
  ext ⟨⟨y, f⟩, d⟩ ⟨a, d'⟩
  simp [cohInj, QuantumRuntime.queryEquivOut, QuantumRuntime.queryEquivIn,
    Matrix.blockDiagonal'_apply_eq]

/-- **One call, coherently.** Embedding the input of a call of port `i` into the coherent
register, calling the coherent port, and projecting back onto the summand `i` is the call of
port `i`. -/
theorem branch_cohProject_comp_queryStep_comp_cohEmbed (i : P) (F : QReg) {A : QReg}
    (ℓ : A ≃ In i × F) :
    ((cohProject.{v} (In := In) i F).frame E.S).branch PUnit.unit ∘ₗ
      ((E.coherent.toRuntime.queryStep (A := QReg.of (cohIn In × F)) () F
        (Equiv.refl _)).branch () ∘ₗ ((cohEmbed.{v} i F ℓ).frame E.S).branch PUnit.unit) =
      (E.toRuntime.queryStep i F ℓ).branch () := by
  rw [E.coherent.toRuntime.queryStep_branch_eq_conj (M := E.coherent.U ()) rfl,
    E.toRuntime.queryStep_branch_eq_conj (M := E.U i) rfl, SubInstrument.branch_frame_apply,
    SubInstrument.branch_frame_apply]
  change LinearMap.comp ((MatrixMap.conj _).amplify E.S)
    (LinearMap.comp _ ((MatrixMap.conj _).amplify E.S)) = _
  rw [MatrixMap.amplify_conj, MatrixMap.amplify_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
  exact congrArg MatrixMap.conj ((Matrix.mul_assoc _ _ _).symm.trans (E.cohCall_matrix i F ℓ))

/-- **The coherent translation runs as the original program.** Run against the coherent oracle,
`x.toCoherent` has the branches that `x` has against the runtime with one port per unitary. -/
theorem run_toCoherent {A : QReg} (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A) :
    E.coherent.toRuntime.run .instruments x.toCoherent = E.toRuntime.run .instruments x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    exact congrArg (((LocalSig.Interp.instruments o).frame E.S).bind) (funext ih)
  | queryBind _ i F ℓ k ih =>
    refine DSubInstrument.ext (funext fun p ↦ ?_)
    change ((((cohEmbed.{v} i F ℓ).toD).frame E.S).bind fun _ ↦
        ((E.coherent.toRuntime.queryStep (A := QReg.of (cohIn In × F)) () F
          (Equiv.refl _)).toD).bind fun _ ↦
          (((cohProject.{v} (In := In) i F).toD).frame E.S).bind fun _ ↦
            E.coherent.toRuntime.run .instruments (k ()).toCoherent).branch p =
      ((E.toRuntime.queryStep i F ℓ).toD.bind fun r ↦ E.toRuntime.run .instruments (k r)).branch p
    simp only [ih, DSubInstrument.branch_bind_apply_univ, Fintype.sum_unique, LinearMap.comp_assoc]
    exact congrArg (LinearMap.comp _)
      (branch_cohProject_comp_queryStep_comp_cohEmbed.{v} E i F ℓ)

/-- The input of a call made coherently, compressed onto the index `i`, has the trace of the
original state when the call is of port `i`, and no trace otherwise. -/
theorem trace_conj_indexProj_callInput_cohEmbed (i i' : P) (F : QReg) {A : QReg}
    (ℓ : A ≃ In i' × F) (ρ : Matrix (A × E.S) (A × E.S) ℂ) :
    (MatrixMap.conj (E.indexProj i) (QuantumRuntime.callInput (Equiv.refl (cohIn In × F)) E.S
      (((cohEmbed.{v} i' F ℓ).frame E.S).branch PUnit.unit ρ))).trace =
      if i' = i then ρ.trace else 0 := by
  set σ := ((cohEmbed.{v} i' F ℓ).frame E.S).branch PUnit.unit ρ with hσ
  have h1 : (MatrixMap.conj (E.indexProj i) (QuantumRuntime.callInput
      (Equiv.refl (cohIn In × F)) E.S σ)).trace =
      ∑ q : (cohIn In × F) × E.S, if q.1.1.1 = i then σ q q else 0 := by
    rw [trace_conj_indexProj]
    conv_rhs => rw [← (QuantumRuntime.queryEquivIn (Equiv.refl (cohIn In × F)) E.S).symm.sum_comp
      (fun q : (cohIn In × F) × E.S ↦ if q.1.1.1 = i then σ q q else 0), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [QuantumRuntime.callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
      SubInstrument.relabel_branch_apply, Matrix.submatrix_apply]
    split_ifs with h
    · exact Finset.sum_congr rfl fun f _ ↦ (ite_eq_left_of_eq_true _ _ (eq_true h)).symm
    · exact (Finset.sum_eq_zero fun f _ ↦ ite_eq_right_of_eq_false _ _ (eq_false h)).symm
  set g : A × E.S → (cohIn In × F) × E.S := Prod.map (cohInj i' F ∘ ℓ) id
  have hg : Function.Injective g :=
    ((cohInj_injective i' F).comp ℓ.injective).prodMap Function.injective_id
  have h2 : σ = MatrixMap.conj (basisMatrix g) ρ := by
    rw [hσ, SubInstrument.branch_frame_apply]
    change (MatrixMap.conj _).amplify E.S ρ = _
    rw [MatrixMap.amplify_conj, basisMatrix_kronecker_one]
  set w : (cohIn In × F) × E.S → ℂ := fun q ↦ if q.1.1.1 = i then 1 else 0
  have h3 : (∑ q : (cohIn In × F) × E.S, if q.1.1.1 = i then σ q q else 0) =
      (Matrix.diagonal w * σ).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, w, ite_mul, one_mul,
      zero_mul]
  rw [h1, h3, h2, MatrixMap.conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    conjTranspose_basisMatrix_mul_mul_basisMatrix, Matrix.submatrix_diagonal _ _ hg]
  have hw : w ∘ g = fun _ ↦ if i' = i then 1 else 0 := rfl
  rw [hw]
  split_ifs <;> simp [Matrix.trace]

/-- **Masses of the coherent translation, call by call.** For a weight on the ports of `x` that
is the trace on the port `i` and zero elsewhere, the weight of the `j`-th call of `x` is the
mass on `i` of the `j`-th call of `x.toCoherent`. -/
theorem queryWeight_toCoherent (i : P)
    {w : ∀ i', Matrix ((uSpec P In).In i' × E.S) ((uSpec P In).In i' × E.S) ℂ → ℝ≥0∞}
    (hw : ∀ i' σ, w i' σ = if i' = i then ENNReal.ofReal σ.trace.re else 0) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (j : ℕ) :
    E.coherent.toRuntime.queryWeight .instruments
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re) x.toCoherent ρ j =
      E.toRuntime.queryWeight .instruments w x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i' F ℓ k ih =>
    cases j with
    | zero =>
      change ∑' b : PUnit.{v + 1}, ENNReal.ofReal (MatrixMap.conj (E.indexProj i)
          (QuantumRuntime.callInput (Equiv.refl (cohIn In × F)) E.S
            (((cohEmbed.{v} i' F ℓ).frame E.S).branch b ρ))).trace.re =
        w i' (QuantumRuntime.callInput ℓ E.S ρ)
      rw [tsum_fintype, Fintype.sum_unique, hw, QuantumRuntime.trace_callInput]
      change ENNReal.ofReal (MatrixMap.conj (E.indexProj i) (QuantumRuntime.callInput
        (Equiv.refl (cohIn In × F)) E.S (((cohEmbed.{v} i' F ℓ).frame E.S).branch PUnit.unit
          ρ))).trace.re = _
      rw [E.trace_conj_indexProj_callInput_cohEmbed]
      split_ifs <;> simp
    | succ j =>
      change ∑' b : PUnit.{v + 1}, ∑' r : Unit, ∑' b' : PUnit.{v + 1},
          E.coherent.toRuntime.queryWeight .instruments
            (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re)
            (k ()).toCoherent (((cohProject.{v} (In := In) i' F).frame E.S).branch b'
              ((E.coherent.toRuntime.queryStep (A := QReg.of (cohIn In × F)) () F
                (Equiv.refl _)).branch r (((cohEmbed.{v} i' F ℓ).frame E.S).branch b ρ))) j =
        ∑' r : Unit, E.toRuntime.queryWeight .instruments w (k r)
          ((E.toRuntime.queryStep i' F ℓ).branch r ρ) j
      simp only [tsum_fintype, Fintype.sum_unique]
      exact (congrArg (fun σ ↦ E.coherent.toRuntime.queryWeight .instruments
          (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re)
          (k ()).toCoherent σ j)
        (LinearMap.congr_fun (branch_cohProject_comp_queryStep_comp_cohEmbed.{v} E i' F ℓ)
          ρ)).trans
        (ih () _ j)

/-- **Masses of the coherent translation** (design §2.5): the total mass on `i` of
`x.toCoherent` against the coherent oracle is the query mass of the port `i` of `x` against the
runtime with one port per unitary. -/
theorem totalMass_toCoherent {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    E.totalMass .instruments x.toCoherent ρ i = E.toRuntime.queryMass .instruments x ρ i := by
  rw [QuantumRuntime.queryMass_eq_totalWeight]
  exact tsum_congr fun j ↦ E.queryWeight_toCoherent i
    (fun i' σ ↦ by by_cases h : i' = i <;> simp [h]) x ρ j

end bridge

end EmulatedOracle

end Quantum
