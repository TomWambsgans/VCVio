/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Oracle.Emulated

/-!
# Emulated oracle regression tests

A two-port emulated oracle on qubits with a qubit of private state: port `0` is the identity,
port `1` swaps the port qubit with the private qubit. Its runtime has lossless steps given by the
Kraus maps of the unitaries; extending it by a further port keeps the old ports; adjoining an
untouched register agrees with the general runtime combinator.

A program making one call of port `1` is translated to the coherent port: the translation runs
as the original program, makes at most `∑ i, 1` coherent calls, has the per-port query masses as
its masses, puts no mass on the index `0`, and satisfies the budget form of Remark 4.2.

Classical calls from inside an experiment elaborate against the signature of unitary ports: a
basis call is lossless and makes one call, a conjunction of checks over a set of indices adds
their budgets, a classical algorithm answered by basis calls is within `n` times the budget of
one call, and the classical reading of a fixed-register program keeps its budget.
-/

public section

open Quantum Matrix
open scoped ENNReal ComplexOrder

namespace VCVioTest.QuantumEmulated

/- Registers and signatures are written as notations rather than constants, so that no
finiteness instance is evaluated when the module is loaded. -/

/-- The qubit register. -/
local notation "Qubit" => QReg.of (Fin 2)

/-- The signature of two unitary ports on qubits. -/
local notation "spec2" => uSpec (Fin 2) fun _ ↦ QReg.of (Fin 2)

/-- Ports of a sum of signatures are the sum of the ports. -/
example : ((spec2).sum (uSpec Unit fun _ ↦ Qubit)).Port = (Fin 2 ⊕ Unit) :=
  rfl

/-- Unitary ports return no classical result. -/
example (i : Fin 2) : (spec2).Result i = Unit :=
  rfl

/-- The unitaries of the swap oracle: the identity on port `0`, the swap of the port qubit with
the private qubit on port `1`. -/
noncomputable def swapU (i : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  if i = 0 then 1 else basisMatrix (Equiv.prodComm (Fin 2) (Fin 2))

/-- The unitaries of the swap oracle are unitary. -/
theorem swapU_mem_unitaryGroup (i : Fin 2) :
    swapU i ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  unfold swapU
  split_ifs
  · exact one_mem _
  · exact Matrix.mem_unitaryGroup_iff'.mpr
      (conjTranspose_basisMatrix_mul_self (Equiv.injective _))

/-- The swap oracle: two ports on qubits, one qubit of private state starting in `|0⟩`. -/
noncomputable def swapOracle : EmulatedOracle (Fin 2) fun _ ↦ Qubit where
  S := Qubit
  init := SubState.basis 0
  U := swapU
  unitary := swapU_mem_unitaryGroup

/-- The steps of the runtime are lossless. -/
example (i : Fin 2) : (swapOracle.toRuntime.step i).Lossless :=
  swapOracle.lossless_toRuntime_step i

/-- Each step is the Kraus map of its unitary. -/
example (i : Fin 2) (r : Unit) :
    (swapOracle.toRuntime.step i).branch r = MatrixMap.conj (swapU i) :=
  swapOracle.toRuntime_step_branch i r

/-- Extending by a further identity port keeps the old ports. -/
example :
    (swapOracle.extend (P' := Unit) (In' := fun _ ↦ Qubit) (fun _ ↦ 1)
      (fun _ ↦ one_mem _)).toRuntime.step (.inl 1) = swapOracle.toRuntime.step 1 :=
  swapOracle.toRuntime_extend_step_inl _ _ 1

/-- The general extension of a runtime answers the new ports by the added steps. -/
example (s : Unit → SubInstrument (Qubit × swapOracle.toRuntime.D)
      (Qubit × swapOracle.toRuntime.D) Unit) :
    ((swapOracle.toRuntime.extend (t := uSpec Unit fun _ ↦ Qubit) s).step (.inr ())) = s () :=
  rfl

/-- The two ways of adjoining an untouched register agree. -/
example :
    (swapOracle.addRegister Qubit (SubState.basis 1)).toRuntime =
      swapOracle.toRuntime.addRegister Qubit (SubState.basis 1) :=
  swapOracle.toRuntime_addRegister _ _

/-- The register of a program holding one qubit and nothing beside it. -/
local notation "Reg" => QReg.of (Fin 2 × Unit)

/-- One call of the swap port on the program's qubit. -/
noncomputable def oneCall :=
  QuantumComp.query (L := LocalSig.instruments.{0}) (spec := spec2) (A := Reg) 1 (QReg.of Unit)
    (Equiv.refl _)

/-- One call of the swap port is within a budget of one call per port. -/
theorem isQueryBound_oneCall : oneCall.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos

/-- The coherent translation makes at most the total budget of calls. -/
theorem isQueryBound_toCoherent_oneCall :
    oneCall.toCoherent.IsQueryBound fun _ ↦ ∑ _ : Fin 2, 1 :=
  QuantumComp.isQueryBound_toCoherent isQueryBound_oneCall

/-- The coherent translation runs as the original program. -/
example :
    swapOracle.coherent.toRuntime.run .instruments oneCall.toCoherent =
      swapOracle.toRuntime.run .instruments oneCall :=
  swapOracle.run_toCoherent oneCall

/-- The masses of the coherent translation are the per-port query masses. -/
example (ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ) (i : Fin 2) :
    swapOracle.totalMass .instruments oneCall.toCoherent ρ i =
      swapOracle.toRuntime.queryMass .instruments oneCall ρ i :=
  swapOracle.totalMass_toCoherent oneCall ρ i

/-- A call of port `1` puts no mass on the index `0`. -/
theorem totalMass_toCoherent_oneCall_zero {ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ}
    (hρ : ρ.PosSemidef) : swapOracle.totalMass .instruments oneCall.toCoherent ρ 0 = 0 := by
  rw [swapOracle.totalMass_toCoherent]
  have h : oneCall.IsQueryBound (Pi.single 1 1) :=
    (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr (by simp)
  have h0 := swapOracle.toRuntime.queryMass_le_of_isQueryBoundAt .instruments (h 0) hρ
  simpa using h0

/-- **Remark 4.2 with a budget.** The masses on the indices add up to at most the number of
coherent calls times the trace. -/
example {ρ : Matrix (Reg × swapOracle.S) (Reg × swapOracle.S) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, swapOracle.totalMass .instruments oneCall.toCoherent ρ i ≤
      (∑ _ : Fin 2, 1 : ℕ) * ENNReal.ofReal ρ.trace.re :=
  swapOracle.sum_totalMass_le .instruments (isQueryBound_toCoherent_oneCall ()) hρ

/-- A basis call of the swap port on the input `|0⟩`, reading the output qubit. -/
noncomputable def swapCall : QComp spec2 (QReg.of Unit) (QReg.of Unit) (Fin 2) :=
  QComp.callBasis (spec := spec2) 1 (QReg.of Unit) 0 fun o _ ↦ o

/-- A basis call is lossless. -/
example : swapCall.Lossless .instruments :=
  QComp.lossless_callBasis _ _ _ _

/-- A basis call makes one call of its port. -/
example : swapCall.IsQueryBound (Pi.single 1 1) :=
  QComp.isQueryBound_callBasis_single _ _ _ _

/-- Check that a basis call of every port on the input `|0⟩` returns `0`. -/
noncomputable def allZero : QComp spec2 (QReg.of Unit) (QReg.of Unit) Bool :=
  QComp.allIn Finset.univ fun i : Fin 2 ↦
    QComp.callBasis (spec := spec2) i (QReg.of Unit) 0 fun o _ ↦ decide (o = 0)

/-- The conjunction of checks adds their budgets. -/
example : allZero.IsQueryBound (∑ i : Fin 2, Pi.single i 1) :=
  QComp.isQueryBound_allIn _ _ fun _ _ ↦ QComp.isQueryBound_callBasis_single _ _ _ _

/-- The conjunction of lossless checks is lossless. -/
example : allZero.Lossless .instruments :=
  QComp.lossless_allIn _ _ fun _ _ ↦ QComp.lossless_callBasis _ _ _ _

/-- Answer the classical queries `t : Fin 2` by basis calls of port `t` on the input `|t⟩`. -/
noncomputable def basisImpl :
    QueryImpl (Fin 2 →ₒ Fin 2) (QComp spec2 (QReg.of Unit) (QReg.of Unit)) :=
  fun t ↦ QComp.callBasis (spec := spec2) t (QReg.of Unit) t fun o _ ↦ o

/-- A classical algorithm making `n` queries runs within `n` basis calls of every port. -/
example {oa : OracleComp (Fin 2 →ₒ Fin 2) Bool} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n) :
    (oa.toQuantumAt basisImpl).IsQueryBound (n • fun _ ↦ 1) :=
  OracleComp.isQueryBound_toQuantumAt (fun _ ↦ QComp.isQueryBound_callBasis Nat.one_pos _ _ _) h

/-- A classical algorithm that returns at once runs to the program that returns at once. -/
example (b : Bool) :
    (pure b : OracleComp (Fin 2 →ₒ Fin 2) Bool).toQuantumAt basisImpl = QuantumComp₂.pure b :=
  OracleComp.toQuantumAt_pure basisImpl b

/-- Reading a fixed-register program as a general program keeps its budget. -/
example : swapCall.forgetReg.IsQueryBound (Pi.single 1 1) :=
  QuantumComp₂.isQueryBound_forgetReg (QComp.isQueryBound_callBasis_single _ _ _ _)

end VCVioTest.QuantumEmulated
