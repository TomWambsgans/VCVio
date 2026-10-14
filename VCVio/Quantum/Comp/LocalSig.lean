/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.DSubInstrument
public import VCVio.Quantum.Register

/-!
# Primitive signatures

A primitive signature (`Quantum.LocalSig`) names the local operations that a program may apply
to its own register, without saying what they do. For each register `A` it gives a type of
operations `Op A`; each operation `o` has a type of classical outcomes `Outcome o`, and on outcome
`b` the program holds the register `next o b`. The register after an operation may depend on its
outcome: a measurement may keep or discard a qubit according to what it reads.

An interpretation (`Quantum.LocalSig.Interp`) gives every operation its meaning, a dependent
subinstrument from `A` with outcomes in `Outcome o` and output register `next o b` on outcome
`b`. Syntax and meaning are kept apart: programs (`Quantum.QuantumComp`) are written over a
signature, and an interpretation is supplied when they are run
(`Quantum.QuantumRuntime.run`). The same program can therefore be read against several
interpretations, and properties of its tree, such as a count of its operations
(`Quantum.QuantumComp.IsCostBound`), do not depend on any of them.

* `Quantum.LocalSig.instruments`: every dependent subinstrument is an operation, and the
  interpretation `Quantum.LocalSig.Interp.instruments` sends it to itself. Programs over this
  signature (`Quantum.QComp`) may apply any subinstrument as one step.
* A gate set is a signature whose operations are finitely many named gates, interpreted by their
  channels; the cost of a program in gates is read off its tree.

## Main definitions

* `Quantum.LocalSig`, with `Quantum.LocalSig.OutcomeAt o u`, the outcomes of `o` that leave the
  register `u`.
* `Quantum.LocalSig.Interp L` and `Quantum.LocalSig.Interp.Lossless`.
* `Quantum.LocalSig.instruments`, whose operations are `Quantum.LocalSig.InstrumentOp`, and
  `Quantum.LocalSig.Interp.instruments`.
-/

public section

namespace Quantum

/-- **Primitive signatures.** For each register `A`, a type of local operations `Op A`; each
operation `o` has a type of classical outcomes `Outcome o`, and on outcome `b` it leaves the
register `next o b`. -/
structure LocalSig where
  /-- The local operations on the register `A`. -/
  Op : QReg → Type 1
  /-- The classical outcomes of an operation. -/
  Outcome : {A : QReg} → Op A → Type
  /-- The register after an operation, as a function of its outcome. -/
  next : {A : QReg} → (o : Op A) → Outcome o → QReg

namespace LocalSig

variable (L : LocalSig)

/-- The outcomes of the operation `o` that leave the register `u`. -/
abbrev OutcomeAt {A : QReg} (o : L.Op A) (u : QReg) : Type :=
  {b : L.Outcome o // L.next o b = u}

/-- **Interpretations.** An interpretation of the signature `L` sends each operation
`o : L.Op A` to a dependent subinstrument from `A` with outcomes in `L.Outcome o`, whose output
register on outcome `b` is `L.next o b`. -/
@[expose]
def Interp : Type 1 :=
  ∀ ⦃A : QReg⦄ (o : L.Op A), DSubInstrument A (L.Outcome o) fun b ↦ L.next o b

variable {L}

/-- An interpretation is lossless when it sends every operation to a lossless dependent
subinstrument. -/
@[expose]
def Interp.Lossless (I : L.Interp) : Prop :=
  ∀ ⦃A : QReg⦄ (o : L.Op A), (I o).Lossless

/-- The operations of the signature of instruments on `A`: a type of outcomes `ι`, output
registers `B : ι → QReg`, and a dependent subinstrument from `A` with these outcomes and
outputs. -/
abbrev InstrumentOp (A : QReg) : Type 1 :=
  Σ (ι : Type) (B : ι → QReg), DSubInstrument A ι fun i ↦ B i

/-- The outcomes of an operation of the signature of instruments. -/
abbrev InstrumentOp.Outcome {A : QReg} (o : InstrumentOp A) : Type :=
  o.1

/-- The register an operation of the signature of instruments leaves on each outcome. -/
abbrev InstrumentOp.next {A : QReg} (o : InstrumentOp A) : o.Outcome → QReg :=
  o.2.1

/-- **The signature of instruments.** An operation on `A` is a dependent subinstrument from `A`,
with any type of outcomes `ι` and output registers `B : ι → QReg`
(`Quantum.LocalSig.InstrumentOp`). -/
@[expose, reducible]
def instruments : LocalSig where
  Op := InstrumentOp
  Outcome := InstrumentOp.Outcome
  next := InstrumentOp.next

/-- The canonical interpretation of the signature of instruments: every operation means the
dependent subinstrument it is. -/
@[expose]
def Interp.instruments : instruments.Interp :=
  fun _ o ↦ o.2.2

/-- The canonical interpretation sends an operation to the dependent subinstrument it is. -/
@[simp]
theorem Interp.instruments_apply {A : QReg} (o : LocalSig.instruments.Op A) :
    Interp.instruments o = o.2.2 :=
  rfl

end LocalSig

end Quantum
