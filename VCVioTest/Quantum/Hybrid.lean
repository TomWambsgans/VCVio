/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.HybridMeasure
public import VCVio.Quantum.Oracle.Basis

/-!
# Query-mass and square-root hybrid regression tests

Tests for the query masses of ePrint 2025/2166, §4.2, the square-root hybrid bound of its
Lemma 5.7, and its Cor 5.8 on leaving a subspace.

* **Identical runtimes.** For any program, the error term of Lemma 5.7 for a runtime against
  itself vanishes, in its Kraus-weight form and in its mass form. The bound of Cor 5.8 vanishes
  when every compressed step commutes with the purified measurement.
* **One call.** A program that calls once puts the trace of its input on its first call and
  nothing on later ones. Against the identity step and the failing step, from any input, both
  sides of Lemma 5.7 compute to `√tr ρ`: the bound is attained.
* **An adaptive program** measures a bit and calls only when it reads `1`. Its mass splits over
  the two outcomes and is the weight of reading `1`: it is the trace of the runtime's initial
  state on `|1⟩` and zero on `|0⟩`, and there is never a second call.
-/

public section

open Quantum Matrix QuantumRuntime Hybrid
open scoped ComplexOrder ENNReal Kronecker Matrix.Norms.L2Operator

namespace VCVioTest.QuantumHybrid

/-! ## Identical runtimes -/

section Identical

variable {spec : QuantumOracleSpec} {L : LocalSig} (I : L.Interp) {X : QReg → Type*} {A D : QReg}
  {σ : SubState D} {s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}

/-- The Kraus weight of the zero family vanishes. -/
theorem krausWeight_zero :
    krausWeight (spec := spec) (D := D) (fun _ _ ↦ 0) = fun _ _ ↦ 0 := by
  funext i τ
  simp [krausWeight]

/-- **A runtime against itself**: the error term of Lemma 5.7 vanishes for every program. -/
theorem tsum_rpow_queryWeight_sub_self (x : QuantumComp L spec X A)
    (ρ : Matrix (A × D) (A × D) ℂ) :
    ∑' j, (QuantumRuntime.mk D σ s).queryWeight I (krausWeight fun i r ↦ U i r - U i r) x ρ j ^
      (2⁻¹ : ℝ) = 0 := by
  have h := fun j ↦ (QuantumRuntime.mk D σ s).queryWeight_const_mul I
    (w := fun _ _ ↦ (0 : ℝ≥0∞)) 0 x ρ j
  simp only [zero_mul] at h
  simp only [sub_self, krausWeight_zero, h,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), tsum_zero]

/-- **A runtime against itself**, in the mass form of Lemma 5.7: the error term vanishes. -/
theorem tsum_rpow_mass_sub_self (x : QuantumComp L spec X A) (ρ : Matrix (A × D) (A × D) ℂ) :
    ∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖U i r - U i r‖ ^ 2)) *
      (QuantumRuntime.mk D σ s).queryMassAt I x ρ i j) ^ (2⁻¹ : ℝ) = 0 := by
  simp [ENNReal.zero_rpow_of_pos]

/-- **Cor 5.8 with commuting steps**: if every compressed step commutes with the purified
measurement of `Q`, a run that starts in `Q` ends in `Q`. -/
theorem tsum_trace_conj_one_sub_eq_zero (hU : ∀ i r, (s i).branch r = MatrixMap.conj (U i r))
    (x : QuantumComp L spec X A) (ρ : SubState A) {P Q : Matrix D D ℂ}
    (hP : (1 - Pᴴ * P).PosSemidef) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hQσ : Q * σ.matrix = σ.matrix)
    (h : (QuantumRuntime.mk D σ s).ForallQueries I (InImageAt P s) x (ρ.matrix ⊗ₖ σ.matrix))
    (hc : ∀ i r, measComm P Q U i r = 0) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (1 - Q))
      ((QuantumRuntime.mk D σ s).jointPost I x ρ p).matrix).trace.re = 0 := by
  refine le_antisymm ((tsum_trace_conj_one_sub_le_of_inImage I hU x ρ hP hQ hQQ hQσ h).trans_eq
    ?_) bot_le
  simp [hc, ENNReal.zero_rpow_of_pos]

end Identical

/-! ## One call -/

/-- One port with trivial input and output registers and a single result: a call acts on the
runtime register only. -/
@[expose, reducible]
def unitSpec : QuantumOracleSpec where
  Port := Unit
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Unit

/-- Call once, with the trivial rest `Unit`, and stop. -/
@[expose]
noncomputable def oneCall {L : LocalSig} :
    QuantumComp L unitSpec (fun _ ↦ Unit) (QReg.of (Unit × Unit)) :=
  QuantumComp.queryBind () (QReg.of Unit) (Equiv.refl (Unit × Unit)) fun _ ↦ QuantumComp.pure ()

section OneCall

variable {L : LocalSig} (I : L.Interp)

/-- The first call of `oneCall` carries the trace of the input. -/
theorem queryMassAt_oneCall_zero (R : QuantumRuntime unitSpec)
    (ρ : Matrix (QReg.of (Unit × Unit) × R.D) (QReg.of (Unit × Unit) × R.D) ℂ) :
    R.queryMassAt I oneCall ρ () 0 = ENNReal.ofReal ρ.trace.re :=
  R.queryMassAt_queryBind_self_zero I () _ _ _ ρ

/-- There is no second call. -/
theorem queryMassAt_oneCall_succ (R : QuantumRuntime unitSpec)
    (ρ : Matrix (QReg.of (Unit × Unit) × R.D) (QReg.of (Unit × Unit) × R.D) ℂ) (j : ℕ) :
    R.queryMassAt I oneCall ρ () (j + 1) = 0 := by
  simp [oneCall]

/-- The total mass of `oneCall` is the trace of the input. -/
theorem queryMass_oneCall (R : QuantumRuntime unitSpec)
    (ρ : Matrix (QReg.of (Unit × Unit) × R.D) (QReg.of (Unit × Unit) × R.D) ℂ) :
    R.queryMass I oneCall ρ () = ENNReal.ofReal ρ.trace.re := by
  simp [oneCall, queryMass_queryBind_self]

/-- The identity step on the runtime register `Fin 2`, with the single Kraus operator `1`. -/
@[expose]
noncomputable def idStep : SubInstrument (Unit × Fin 2) (Unit × Fin 2) Unit :=
  SubInstrument.ofKraus (fun _ ↦ 1) (by simp)

/-- The runtime on `Fin 2`, started at `|0⟩`, whose calls do nothing. -/
@[expose, reducible]
noncomputable def idRuntime : QuantumRuntime unitSpec :=
  QuantumRuntime.mk (QReg.of (Fin 2)) (SubState.basis 0) fun _ ↦ idStep

/-- The runtime on `Fin 2`, started at `|0⟩`, whose calls fail. -/
@[expose, reducible]
noncomputable def failRuntime : QuantumRuntime unitSpec :=
  QuantumRuntime.mk (QReg.of (Fin 2)) (SubState.basis 0) fun _ ↦ SubInstrument.fail

/-- The Kraus operators of the identity step. -/
theorem idStep_branch (i : unitSpec.Port) (r : unitSpec.Result i) :
    idStep.branch r =
      MatrixMap.conj ((fun _ _ ↦ (1 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r) :=
  rfl

/-- The Kraus operators of the failing step. -/
theorem fail_branch (i : unitSpec.Port) (r : unitSpec.Result i) :
    (SubInstrument.fail : SubInstrument (Unit × Fin 2) (Unit × Fin 2) Unit).branch r =
      MatrixMap.conj ((fun _ _ ↦ (0 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r) := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp [SubInstrument.branch_fail]

/-- Against the identity step, `oneCall` keeps the trace of its input. -/
theorem tsum_trace_run_idRuntime (ρ : SubState (QReg.of (Unit × Unit))) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj (1 : Matrix (p.1 × idRuntime.D) (p.1 × idRuntime.D) ℂ)
      ((idRuntime.run I oneCall).branch p
        (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix))).trace.re =
      ENNReal.ofReal ρ.matrix.trace.re := by
  simp only [MatrixMap.conj_one, LinearMap.id_apply]
  refine (idRuntime.tsum_jointPost_trace I oneCall ρ).trans ?_
  rw [idRuntime.lossless_run I (x := oneCall) (fun _ ↦ trivial)
    (fun _ ↦ SubInstrument.lossless_ofKraus _ (by simp)), SubState.trace_re_prod]
  simp

/-- A call against the failing step fails. -/
theorem branch_queryStep_failRuntime (E : QReg) {A : QReg} (ℓ : A ≃ unitSpec.In () × E)
    (r : Unit) : (failRuntime.queryStep () E ℓ).branch r = 0 := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp [queryStep, SubInstrument.branch_bind_apply, SubInstrument.branch_fail]

/-- Against the failing step, `oneCall` fails. -/
theorem tsum_trace_run_failRuntime (ρ : SubState (QReg.of (Unit × Unit))) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj (1 : Matrix (p.1 × idRuntime.D) (p.1 × idRuntime.D) ℂ)
      ((failRuntime.run I oneCall).branch p
        (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix))).trace.re = 0 := by
  simp only [MatrixMap.conj_one, LinearMap.id_apply]
  refine (failRuntime.tsum_jointPost_trace I oneCall ρ).trans ?_
  rw [oneCall, run_queryBind, DSubInstrument.familyTrace_bind]
  simp [SubInstrument.branch_toD, branch_queryStep_failRuntime]

/-- The error term of Lemma 5.7 for the identity step against the failing step, on `oneCall`, is
the square root of the trace of the input. -/
theorem tsum_rpow_queryWeight_oneCall (ρ : SubState (QReg.of (Unit × Unit))) :
    ∑' j, idRuntime.queryWeight I
        (krausWeight fun i r ↦ (fun _ _ ↦ (1 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r -
          (fun _ _ ↦ (0 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r)
        oneCall (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix) j ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal ρ.matrix.trace.re ^ (2⁻¹ : ℝ) := by
  rw [tsum_eq_single 0 fun j hj ↦ ?_]
  · simp [oneCall, krausWeight, trace_callInput, Matrix.trace_kronecker]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [oneCall, ENNReal.zero_rpow_of_pos]

/-- **Lemma 5.7 is attained** on one call: for the identity step against the failing step, both
sides of the bound are `√tr ρ`. -/
theorem lemma57_oneCall_eq (ρ : SubState (QReg.of (Unit × Unit))) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (1 : Matrix (p.1 × idRuntime.D) (p.1 × idRuntime.D) ℂ)
      ((idRuntime.run I oneCall).branch p
        (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix))).trace.re) ^ (2⁻¹ : ℝ) =
      (∑' p, ENNReal.ofReal (MatrixMap.conj (1 : Matrix (p.1 × idRuntime.D) (p.1 × idRuntime.D) ℂ)
        ((failRuntime.run I oneCall).branch p
          (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix))).trace.re) ^ (2⁻¹ : ℝ) +
      ∑' j, idRuntime.queryWeight I
        (krausWeight fun i r ↦ (fun _ _ ↦ (1 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r -
          (fun _ _ ↦ (0 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r)
        oneCall (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix) j ^ (2⁻¹ : ℝ) := by
  rw [tsum_trace_run_idRuntime, tsum_trace_run_failRuntime, tsum_rpow_queryWeight_oneCall,
    ENNReal.zero_rpow_of_pos (by norm_num), zero_add]

/-- The bound of Lemma 5.7 itself, for the identity step against the failing step. -/
example (ρ : SubState (QReg.of (Unit × Unit))) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (1 : Matrix (p.1 × idRuntime.D) (p.1 × idRuntime.D) ℂ)
      ((idRuntime.run I oneCall).branch p
        (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix))).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (1 : Matrix (p.1 × idRuntime.D) (p.1 × idRuntime.D) ℂ)
        ((failRuntime.run I oneCall).branch p
          (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix))).trace.re) ^ (2⁻¹ : ℝ) +
      ∑' j, idRuntime.queryWeight I
        (krausWeight fun i r ↦ (fun _ _ ↦ (1 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r -
          (fun _ _ ↦ (0 : Matrix (Unit × Fin 2) (Unit × Fin 2) ℂ)) i r)
        oneCall (ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix) j ^ (2⁻¹ : ℝ) :=
  rpow_inv_two_tsum_trace_conj_run_le I (D := QReg.of (Fin 2)) (s₀ := fun _ ↦ idStep)
    (s₁ := fun _ ↦ SubInstrument.fail) (SubState.basis 0) (SubState.basis 0) idStep_branch
    fail_branch oneCall (Z := fun p ↦ p.1 × idRuntime.D) (fun _ ↦ 1)
    (fun _ ↦ by simpa using Matrix.PosSemidef.zero)
    (ρ := ρ.matrix ⊗ₖ (SubState.basis (0 : Fin 2)).matrix)
    (ρ.prod (SubState.basis (0 : Fin 2))).posSemidef

end OneCall

/-! ## An adaptive program -/

/-- Measure the bit of the register `Unit × Fin 2` in the computational basis. -/
@[expose, reducible]
noncomputable def measBit : LocalSig.instruments.Op (QReg.of (Unit × Fin 2)) :=
  ⟨Fin 2, fun _ ↦ QReg.of (Unit × Fin 2),
    SubInstrument.toD (SubInstrument.classical id fun m : Unit × Fin 2 ↦ m.2)⟩

/-- Measure the bit; on `1`, call with the bit as the rest of the register; return the bit. -/
@[expose]
noncomputable def callIfOne :
    QuantumComp LocalSig.instruments unitSpec (fun _ ↦ Fin 2) (QReg.of (Unit × Fin 2)) :=
  QuantumComp.primBind measBit fun b ↦
    if b = 1 then
      QuantumComp.queryBind () (QReg.of (Fin 2)) (Equiv.refl (Unit × Fin 2)) fun _ ↦
        QuantumComp.pure b
    else QuantumComp.pure b

/-- **The mass splits over the branches**: the total mass of `callIfOne` is the trace of the
branch of the measurement on `1`, whatever the runtime. -/
theorem queryMass_callIfOne (R : QuantumRuntime unitSpec)
    (ρ : Matrix (QReg.of (Unit × Fin 2) × R.D) (QReg.of (Unit × Fin 2) × R.D) ℂ) :
    R.queryMass .instruments callIfOne ρ () =
      ENNReal.ofReal (((SubInstrument.classical id fun m : Unit × Fin 2 ↦ m.2).branch 1).amplify
        R.D ρ).trace.re := by
  rw [callIfOne, queryMass_primBind, tsum_fintype, Fin.sum_univ_two]
  simp [queryMass_queryBind_self, DSubInstrument.branch_frame_apply, SubInstrument.branch_toD]

/-- There is never a second call. -/
theorem queryMassAt_callIfOne_succ (R : QuantumRuntime unitSpec)
    (ρ : Matrix (QReg.of (Unit × Fin 2) × R.D) (QReg.of (Unit × Fin 2) × R.D) ℂ) (j : ℕ) :
    R.queryMassAt .instruments callIfOne ρ () (j + 1) = 0 := by
  rw [callIfOne, queryMassAt_primBind, tsum_fintype, Fin.sum_univ_two]
  simp

/-- On a basis input, the mass is the trace of the runtime's initial state if the bit is `1`, and
zero if it is `0`. -/
theorem queryMass_callIfOne_basis (R : QuantumRuntime unitSpec) (c : Fin 2) :
    R.queryMass .instruments callIfOne
        ((SubState.basis ((), c)).matrix ⊗ₖ R.init.matrix) () =
      if c = 1 then ENNReal.ofReal R.init.matrix.trace.re else 0 := by
  rw [queryMass_callIfOne, MatrixMap.amplify_kronecker, SubState.matrix_basis,
    SubInstrument.branch_classical_basis, Matrix.trace_kronecker]
  split_ifs <;> simp_all

end VCVioTest.QuantumHybrid
