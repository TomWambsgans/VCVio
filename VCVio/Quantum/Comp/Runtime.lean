/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.Basic
public import VCVio.Quantum.Oracle.Basis

/-!
# Runtimes and the execution of quantum programs

A runtime interprets the ports of a signature. It owns a private register `D`, which starts in
the substate `init` and persists from one call to the next, and it answers a call of port `i`
with a subinstrument `step i` from `In i × D` to `Out i × D` with outcomes in `Result i`. The
program has no command that acts on `D`: it reaches `D` only through calls.

Running a program `x : QuantumComp spec A B α` against a runtime `R` gives a subinstrument
`R.run x` from `A × R.D` to `B × R.D` with outcomes in `α`, by recursion on the program tree:

* a local subinstrument `p` acts on the program register, framed by `D`;
* a call of port `i` through `ℓ : A ≃ In i × E` relabels `A × D` to `(In i × D) × E`, applies
  `step i` framed by `E`, and relabels `(Out i × D) × E` to `(Out i × E) × D`
  (`Quantum.QuantumRuntime.queryStep`).

`run` is a morphism of indexed monads (`Quantum.QuantumRuntime.run_bind`).

## Observation

A program is observed from a substate `ρ` of its starting register, with the runtime's register
in `init`, that is from the product substate `ρ ⊗ init`:

* `Quantum.QuantumRuntime.jointPost R x ρ a`: the joint substate of `B × D` after the run reports
  `a`. Its trace is the weight of `a`.
* `Quantum.QuantumRuntime.reducedPost R x ρ a`: its reduced substate on the program register
  `B`, which is all a later program can act on.
* `Quantum.QuantumRuntime.outcomeLaw R x ρ`: the law of the returned value, a subprobability
  measure whose missing mass is failure.

## Main definitions

* `Quantum.QuantumRuntime spec`: a private register, its initial substate and a step per port.
* `Quantum.QuantumRuntime.queryStep` and `Quantum.QuantumRuntime.run`.
* `Quantum.QuantumRuntime.jointPost`, `Quantum.QuantumRuntime.reducedPost` and
  `Quantum.QuantumRuntime.outcomeLaw`.

## Main statements

* `Quantum.QuantumRuntime.run_pure`, `run_act`, `run_query`, `run_bind` and `run_map`.
* `Quantum.QuantumRuntime.lossless_run`: a lossless program against lossless steps runs to a
  lossless subinstrument.
-/

public section

open IPFunctor MeasureTheory
open scoped Kronecker

namespace Quantum

/-- A runtime for the signature `spec`: a private register `D` with initial substate `init`, and
for each port the subinstrument that answers a call of it. -/
structure QuantumRuntime (spec : QuantumOracleSpec) where
  /-- The runtime's private register, which persists across calls. -/
  D : QReg
  /-- The initial substate of the private register. -/
  init : SubState D
  /-- The subinstrument that answers a call of port `i`, acting on the port's input register
  and the private register. -/
  step : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)

namespace QuantumRuntime

/-! ## The relabellings of a call -/

/-- The bijection that brings a port's input register next to the runtime register before a
call: `A × D ≃ (I × D) × E` for `ℓ : A ≃ I × E`. -/
@[expose]
def queryEquivIn {A I E : Type*} (ℓ : A ≃ I × E) (D : Type*) : A × D ≃ (I × D) × E :=
  (ℓ.prodCongr (Equiv.refl D)).trans
    ((Equiv.prodAssoc I E D).trans
      ((Equiv.prodCongr (Equiv.refl I) (Equiv.prodComm E D)).trans
        (Equiv.prodAssoc I D E).symm))

/-- The bijection that puts the program's remainder register back after a call:
`(O × D) × E ≃ (O × E) × D`. -/
@[expose]
def queryEquivOut (O D E : Type*) : (O × D) × E ≃ (O × E) × D :=
  (Equiv.prodAssoc O D E).trans
    ((Equiv.prodCongr (Equiv.refl O) (Equiv.prodComm D E)).trans (Equiv.prodAssoc O E D).symm)

/-- `queryEquivIn` on a basis element. -/
@[simp]
theorem queryEquivIn_apply {A I E : Type*} (ℓ : A ≃ I × E) (D : Type*) (x : A × D) :
    queryEquivIn ℓ D x = (((ℓ x.1).1, x.2), (ℓ x.1).2) :=
  rfl

/-- `queryEquivOut` on a basis element. -/
@[simp]
theorem queryEquivOut_apply (O D E : Type*) (x : (O × D) × E) :
    queryEquivOut O D E x = ((x.1.1, x.2), x.1.2) :=
  rfl

variable {spec : QuantumOracleSpec} (R : QuantumRuntime spec) {A B C : QReg} {α β : Type}

/-! ## Execution -/

/-- One call of port `i`, with the rest `E` of the program register carried along: relabel
`A × D` to `(In i × D) × E`, apply the port's step framed by `E`, and relabel back. -/
@[expose]
noncomputable def queryStep (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    SubInstrument (A × R.D) ((spec.Out i × E) × R.D) (spec.Result i) :=
  (SubInstrument.relabel (queryEquivIn ℓ R.D)).bind fun _ ↦
    ((R.step i).frame E).bind fun r ↦
      (SubInstrument.relabel (queryEquivOut (spec.Out i) R.D E)).bind fun _ ↦
        SubInstrument.pure r

/-- Execution of a program tree, by recursion on the tree. -/
@[expose]
noncomputable def runAux {B : QReg} :
    {A : QReg} → IFreeM spec.toIPFunctor (fun u ↦ PSigma fun _ : u = B ↦ α) A →
      SubInstrument (A × R.D) (B × R.D) α
  | _, .pure ⟨rfl, a⟩ => SubInstrument.pure a
  | _, .liftBind (.act _ _ p) k => (p.frame R.D).bind fun b ↦ runAux (k b)
  | _, .liftBind (.query i E ℓ) k => (R.queryStep i E ℓ).bind fun r ↦ runAux (k r)

/-- **Execution.** A program against a runtime is a subinstrument on the joint register of the
program and the runtime. -/
@[expose]
noncomputable def run (x : QuantumComp spec A B α) : SubInstrument (A × R.D) (B × R.D) α :=
  R.runAux x

/-- Running a program that returns `a` returns `a` and leaves the state unchanged. -/
@[simp]
theorem run_pure (a : α) :
    R.run (QuantumComp.pure (spec := spec) (A := A) a) = SubInstrument.pure a :=
  rfl

/-- Running a local subinstrument applies it framed by the runtime register. -/
theorem run_act (p : SubInstrument A B α) :
    R.run (QuantumComp.act (spec := spec) p) = (p.frame R.D).bind fun a ↦ SubInstrument.pure a :=
  rfl

/-- Running a call applies `queryStep`. -/
theorem run_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    R.run (QuantumComp.query i E ℓ) = (R.queryStep i E ℓ).bind fun r ↦ SubInstrument.pure r :=
  rfl

/-- Running a local subinstrument followed by a continuation. -/
@[simp]
theorem run_act_bind (p : SubInstrument A B β) (k : β → QuantumComp spec B C α) :
    R.run ((QuantumComp.act p).bind k) = (p.frame R.D).bind fun b ↦ R.run (k b) :=
  rfl

/-- Running a call followed by a continuation. -/
@[simp]
theorem run_query_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp spec (QReg.of (spec.Out i × E)) C α) :
    R.run ((QuantumComp.query i E ℓ).bind k) =
      (R.queryStep i E ℓ).bind fun r ↦ R.run (k r) :=
  rfl

/-- `run` is a morphism of indexed monads: running a sequence of programs is sequencing their
runs. -/
theorem run_bind (x : QuantumComp spec A B α) (k : α → QuantumComp spec B C β) :
    R.run (x.bind k) = (R.run x).bind fun a ↦ R.run (k a) := by
  refine QuantumComp.inductionOn (motive := fun A B x ↦ ∀ {C : QReg}
    (k : α → QuantumComp spec B C β), R.run (x.bind k) = (R.run x).bind fun a ↦ R.run (k a))
    ?_ ?_ ?_ x k
  · intro _ a _ k
    exact (SubInstrument.pure_bind a fun a ↦ R.run (k a)).symm
  · intro _ _ _ _ p k' ih _ k
    rw [QuantumComp.bind_assoc, run_act_bind, run_act_bind, SubInstrument.bind_assoc]
    exact congrArg _ (funext fun b ↦ ih b k)
  · intro _ _ i E ℓ k' ih _ k
    rw [QuantumComp.bind_assoc, run_query_bind, run_query_bind, SubInstrument.bind_assoc]
    exact congrArg _ (funext fun r ↦ ih r k)

/-- Running a program with a relabelled return value relabels the outcomes of its run. -/
theorem run_map (f : α → β) (x : QuantumComp spec A B α) : R.run (x.map f) = (R.run x).map f := by
  rw [QuantumComp.map_eq_bind_pure, run_bind, SubInstrument.map_eq_bind_pure]
  rfl

/-- A call against a lossless step is lossless. -/
theorem lossless_queryStep {i : spec.Port} (hi : (R.step i).Lossless) (E : QReg)
    (ℓ : A ≃ spec.In i × E) : (R.queryStep i E ℓ).Lossless :=
  (SubInstrument.lossless_relabel _).bind fun _ ↦ (hi.frame E).bind fun _ ↦
    (SubInstrument.lossless_relabel _).bind fun _ ↦ SubInstrument.lossless_pure _

/-- A lossless program run against a runtime whose steps are lossless is lossless. -/
theorem lossless_run {x : QuantumComp spec A B α} (hx : x.Lossless)
    (hR : ∀ i, (R.step i).Lossless) : (R.run x).Lossless := by
  refine QuantumComp.inductionOn
    (motive := fun A B x ↦ x.Lossless → (R.run x).Lossless) ?_ ?_ ?_ x hx
  · exact fun _ a _ ↦ SubInstrument.lossless_pure a
  · intro _ _ _ _ p k ih hx
    rw [run_act_bind]
    exact (hx.1.frame _).bind fun b ↦ ih b (hx.2 b)
  · intro _ _ i E ℓ k ih hx
    rw [run_query_bind]
    exact (R.lossless_queryStep (hR i) E ℓ).bind fun r ↦ ih r (hx r)

/-! ## Observation -/

/-- The joint substate of the program register and the runtime register after running `x` from
`ρ ⊗ init` and observing the outcome `a`. Its trace is the weight of `a`. -/
@[expose]
noncomputable def jointPost (x : QuantumComp spec A B α) (ρ : SubState A) (a : α) :
    SubState (B × R.D) :=
  (R.run x).post (ρ.prod R.init) a

/-- The substate of the program register after running `x` from `ρ ⊗ init` and observing the
outcome `a`, with the runtime register traced out. -/
@[expose]
noncomputable def reducedPost (x : QuantumComp spec A B α) (ρ : SubState A) (a : α) : SubState B :=
  (R.jointPost x ρ a).traceRight

/-- The law of the value returned by `x` run from `ρ ⊗ init`: a subprobability measure whose
missing mass is the weight of failure. -/
@[expose]
noncomputable def outcomeLaw [MeasurableSpace α] (x : QuantumComp spec A B α) (ρ : SubState A) :
    Measure α :=
  (R.run x).outcomeMeasure (ρ.prod R.init)

/-- The matrix of the joint post-state. -/
@[simp]
theorem matrix_jointPost (x : QuantumComp spec A B α) (ρ : SubState A) (a : α) :
    (R.jointPost x ρ a).matrix = (R.run x).branch a (ρ.matrix ⊗ₖ R.init.matrix) :=
  rfl

/-- The reduced post-state has the trace of the joint post-state. -/
theorem trace_reducedPost (x : QuantumComp spec A B α) (ρ : SubState A) (a : α) :
    (R.reducedPost x ρ a).matrix.trace = (R.jointPost x ρ a).matrix.trace :=
  MatrixMap.trace_traceRight _

/-- Outcome laws are subprobability measures. -/
instance [MeasurableSpace α] (x : QuantumComp spec A B α) (ρ : SubState A) :
    IsSubprobabilityMeasure (R.outcomeLaw x ρ) :=
  SubInstrument.outcomeMeasure.instIsSubprobabilityMeasure _ _

/-- The weight of a single outcome is the trace of the joint post-state. -/
theorem outcomeLaw_apply_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (x : QuantumComp spec A B α) (ρ : SubState A) (a : α) :
    R.outcomeLaw x ρ {a} = ENNReal.ofReal (R.jointPost x ρ a).matrix.trace.re :=
  SubInstrument.outcomeMeasure_apply_singleton _ _ a

/-- When the run is lossless, the outcome law has the product of the traces of `ρ` and `init`
as its total mass. -/
theorem outcomeLaw_apply_univ_of_lossless [MeasurableSpace α] {x : QuantumComp spec A B α}
    (hx : (R.run x).Lossless) (ρ : SubState A) :
    R.outcomeLaw x ρ Set.univ = ENNReal.ofReal (ρ.matrix.trace.re * R.init.matrix.trace.re) := by
  rw [outcomeLaw, hx.outcomeMeasure_apply_univ, SubState.trace_re_prod]

end QuantumRuntime

end Quantum
