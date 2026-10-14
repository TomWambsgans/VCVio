/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.IPFunctor.Free.Indexed
public import VCVio.Quantum.Register
public import VCVio.Quantum.SubInstrument

/-!
# Quantum programs

A quantum program is a tree of commands over a quantum oracle signature. A signature
(`Quantum.QuantumOracleSpec`) names a type of oracle ports; port `i` takes an input register
`In i`, leaves an output register `Out i`, and returns a classical result of type `Result i`.
A program has two kinds of command:

* `Quantum.QuantumComp.act p`: a local subinstrument `p : SubInstrument A B β` on the program's
  own register. It may change the register from `A` to `B`, and its classical outcome `b : β`
  selects the continuation.
* `Quantum.QuantumComp.query i E ℓ`: a call of port `i`. The equivalence `ℓ : A ≃ In i × E`
  exposes the port's input register as a tensor factor of the current register; the rest `E` is
  carried through the call untouched, and the register afterwards is `Out i × E`. The result
  `r : Result i` selects the continuation.

`Quantum.QuantumComp spec A B α` is the free indexed monad on these commands (PolyFun's
`IPFunctor.FreeM₂`), indexed by the register before and after the program. Programs that start
and end on the same register form a lawful monad, and the general case is a lawful indexed
monad. Programs do not mention any oracle: `Quantum.QuantumRuntime` and
`Quantum.QuantumRuntime.run` interpret the queries.

## The general model

This is the general model of quantum oracle programs with a definite causal order, and the
definition every other form of quantum adversary is compared against:

* **Adaptive.** Every continuation sees all classical outcomes so far, so the number of queries,
  their ports and their order, and the point at which the program stops all depend on them.
* **Multi-port.** A signature has any type of ports, each with its own registers and classical
  result type.
* **Register-changing.** Each command changes the register: programs allocate, discard and
  reshape registers between queries, and a program from `A` to `B` is an open stage with quantum
  input and output.
* **Stateful oracles.** An oracle is a runtime with a private register that persists across
  calls (`Quantum.QuantumRuntime`); the program has no command acting on it.

Query budgets are read off the tree (`Quantum.QuantumComp.IsQueryBound`) rather than fixed by a
type index. Fixed-slot adversaries (`Quantum.QuantumComb`) are a derived form: they embed as
straight-line programs (`Quantum.QuantumComb.toComp`).

## Not covered yet

The following are open design questions, not claims about the model:

* **Coherent port choice.** The port of a query is classical. A query whose port is chosen by a
  quantum register is expressed through a single sum port acting on `ι × X × Y`, which is a
  different resource from one call to each port.
* **Outcome-dependent final register.** All leaves of a program end on the same register `B`.
  A program whose final register depends on its classical outcome needs PolyFun's `IFreeM` with
  a leaf family in place of `FreeM₂`.
* **Unbounded loops.** Program trees are well founded, so every path is finite. Unbounded or
  expected-time programs need a coinductive tree and execution as a limit.

## Main definitions

* `Quantum.QuantumOracleSpec`, with its commands `Quantum.QuantumOracleSpec.Cmd` and the indexed
  polynomial functor `Quantum.QuantumOracleSpec.toIPFunctor`.
* `Quantum.QuantumComp spec A B α`, with `act`, `query`, `pure`, `bind` and `map`, the
  induction principle `Quantum.QuantumComp.inductionOn`, and the `Monad`, `LawfulMonad`,
  `IndexedMonad` and `LawfulIndexedMonad` instances.
* `Quantum.QuantumComp.Lossless`: every local subinstrument on every branch is lossless.
-/

public section

open IPFunctor

namespace Quantum

/-- A quantum oracle signature: a type of ports, and for each port an input register, an output
register and a classical result type. -/
structure QuantumOracleSpec where
  /-- The oracle ports. -/
  Port : Type
  /-- The register a call of the port acts on. -/
  In : Port → QReg
  /-- The register a call of the port leaves in place of its input register. -/
  Out : Port → QReg
  /-- The classical result of a call of the port. -/
  Result : Port → Type

namespace QuantumOracleSpec

variable (spec : QuantumOracleSpec)

/-- The commands available to a program whose current register is `A`. -/
inductive Cmd (A : QReg) : Type 1
  /-- A local subinstrument from `A` to `B` with outcomes in `β`. -/
  | act (B : QReg) (β : Type) (p : SubInstrument A B β)
  /-- A call of port `i`; `ℓ` splits the current register into the port's input register and a
  remainder `E` that the call leaves alone. -/
  | query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)

variable {spec}

/-- The classical response of a command: the outcome of a local subinstrument, or the result of
a call. -/
@[expose]
def Cmd.Resp {A : QReg} : spec.Cmd A → Type
  | .act _ β _ => β
  | .query i _ _ => spec.Result i

/-- The register after a command, given its response. -/
@[expose]
def Cmd.next {A : QReg} : (c : spec.Cmd A) → c.Resp → QReg
  | .act B _ _, _ => B
  | .query i E _, _ => QReg.of (spec.Out i × E)

variable (spec)

/-- The commands of a signature as an indexed polynomial endofunctor on registers. -/
@[expose]
def toIPFunctor : IPFunctor.Endo.{1, 1, 0} QReg where
  A := spec.Cmd
  B _ c := c.Resp
  src _ c b := c.next b

end QuantumOracleSpec

/-- **Quantum programs.** A program over the signature `spec` that starts on the register `A`,
ends on the register `B` and returns a value of type `α`. -/
@[expose]
def QuantumComp (spec : QuantumOracleSpec) (A B : QReg) (α : Type) : Type 1 :=
  FreeM₂ spec.toIPFunctor A B α

namespace QuantumComp

variable {spec : QuantumOracleSpec} {A B C D : QReg} {α β γ : Type}

/-! ## Commands and the indexed monad structure -/

/-- Run a local subinstrument on the program's register and return its outcome. -/
@[expose]
def act (p : SubInstrument A B α) : QuantumComp spec A B α :=
  FreeM₂.liftBind (P := spec.toIPFunctor) (.act B α p) fun a ↦ FreeM₂.pure a

/-- Call port `i` on the factor of the register that `ℓ` exposes, and return its result. -/
@[expose]
def query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    QuantumComp spec A (QReg.of (spec.Out i × E)) (spec.Result i) :=
  FreeM₂.liftBind (P := spec.toIPFunctor) (.query i E ℓ) fun r ↦ FreeM₂.pure r

/-- The program that returns `a` without a command. -/
@[expose]
protected def pure (a : α) : QuantumComp spec A A α :=
  FreeM₂.pure a

/-- Sequencing: run `x`, then the program selected by its return value. -/
@[expose]
protected def bind (x : QuantumComp spec A B α) (k : α → QuantumComp spec B C β) :
    QuantumComp spec A C β :=
  FreeM₂.bind x k

/-- Apply `f` to the return value of a program. -/
@[expose]
protected def map (f : α → β) (x : QuantumComp spec A B α) : QuantumComp spec A B β :=
  FreeM₂.map f x

/-! ## Induction -/

/-- Induction on programs: a property of every program follows from the property of `pure a`,
and its preservation by prefixing a local subinstrument or a call to a family of programs. -/
@[elab_as_elim]
protected theorem inductionOn {motive : ∀ A B : QReg, QuantumComp spec A B α → Prop}
    (pure : ∀ (A : QReg) (a : α), motive A A (QuantumComp.pure a))
    (act_bind : ∀ (A B C : QReg) (β : Type) (p : SubInstrument A B β)
      (k : β → QuantumComp spec B C α), (∀ b, motive B C (k b)) →
        motive A C ((act p).bind k))
    (query_bind : ∀ (A C : QReg) (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
      (k : spec.Result i → QuantumComp spec (QReg.of (spec.Out i × E)) C α),
      (∀ r, motive _ C (k r)) → motive A C ((query i E ℓ).bind k))
    {A B : QReg} (x : QuantumComp spec A B α) : motive A B x :=
  FreeM₂.inductionOn (P := spec.toIPFunctor) (C := motive) (fun s a ↦ pure s a)
    (fun s t c r ih ↦ by
      cases c with
      | act B β p => exact act_bind s B t β p r ih
      | query i E ℓ => exact query_bind s t i E ℓ r ih) x

/-! ## Monad laws -/

/-- Left unit law. -/
@[simp]
protected theorem pure_bind (a : α) (k : α → QuantumComp spec A B β) :
    (QuantumComp.pure a).bind k = k a :=
  rfl

/-- Right unit law. -/
@[simp]
protected theorem bind_pure (x : QuantumComp spec A B α) : x.bind QuantumComp.pure = x :=
  ibind_ipure (I := QReg) (M := fun s t α ↦ FreeM₂ spec.toIPFunctor s t α) x

/-- Sequencing of programs is associative. -/
protected theorem bind_assoc (x : QuantumComp spec A B α) (k : α → QuantumComp spec B C β)
    (l : β → QuantumComp spec C D γ) :
    (x.bind k).bind l = x.bind fun a ↦ (k a).bind l :=
  ibind_assoc (I := QReg) (M := fun s t α ↦ FreeM₂ spec.toIPFunctor s t α) x k l

/-- Applying `f` to the return value is sequencing with `fun a ↦ pure (f a)`. -/
theorem map_eq_bind_pure (f : α → β) (x : QuantumComp spec A B α) :
    x.map f = x.bind fun a ↦ QuantumComp.pure (f a) := by
  induction x using FreeM₂.inductionOn with
  | pure _ _ => rfl
  | liftBind _ _ a r ih => exact congrArg (FreeM₂.liftBind a) (funext ih)

/-- Applying the identity to the return value changes nothing. -/
@[simp]
protected theorem map_id (x : QuantumComp spec A B α) : x.map id = x := by
  rw [map_eq_bind_pure]
  exact QuantumComp.bind_pure x

/-- A local subinstrument followed by a continuation is the command with that continuation. -/
theorem act_bind (p : SubInstrument A B β) (k : β → QuantumComp spec B C α) :
    (act p).bind k = FreeM₂.liftBind (P := spec.toIPFunctor) (.act B β p) k :=
  rfl

/-- A call followed by a continuation is the command with that continuation. -/
theorem query_bind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp spec (QReg.of (spec.Out i × E)) C α) :
    (query i E ℓ).bind k = FreeM₂.liftBind (P := spec.toIPFunctor) (.query i E ℓ) k :=
  rfl

/-- Programs that end on the register they start on form a monad. -/
instance : Monad (QuantumComp spec A A) where
  pure := QuantumComp.pure
  bind := QuantumComp.bind
  map := QuantumComp.map

/-- Monadic `pure` on programs is `Quantum.QuantumComp.pure`. -/
@[simp]
theorem pure_eq (a : α) : (pure a : QuantumComp spec A A α) = QuantumComp.pure a :=
  rfl

/-- Monadic bind on programs is `Quantum.QuantumComp.bind`. -/
@[simp]
theorem bind_eq (x : QuantumComp spec A A α) (k : α → QuantumComp spec A A β) :
    x >>= k = x.bind k :=
  rfl

/-- Functorial map on programs is `Quantum.QuantumComp.map`. -/
@[simp]
theorem map_eq (f : α → β) (x : QuantumComp spec A A α) : f <$> x = x.map f :=
  rfl

/-- The monad of programs on a fixed register is lawful. -/
instance : LawfulMonad (QuantumComp spec A A) :=
  LawfulMonad.mk' _
    (id_map := QuantumComp.map_id)
    (pure_bind := QuantumComp.pure_bind)
    (bind_assoc := QuantumComp.bind_assoc)
    (bind_pure_comp := fun f x ↦ (map_eq_bind_pure f x).symm)

/-- Programs form an indexed monad over registers. -/
instance : IndexedMonad QReg (QuantumComp spec) where
  ipure := QuantumComp.pure
  ibind := QuantumComp.bind

/-- The indexed monad of programs is lawful. -/
instance : LawfulIndexedMonad QReg (QuantumComp spec) where
  ipure_ibind := QuantumComp.pure_bind
  ibind_ipure := QuantumComp.bind_pure
  ibind_assoc := QuantumComp.bind_assoc

/-! ## Lossless programs -/

/-- Every local subinstrument on every branch of the tree is lossless. -/
@[expose]
def losslessAux {B : QReg} :
    {A : QReg} → IFreeM spec.toIPFunctor (fun u ↦ PSigma fun _ : u = B ↦ α) A → Prop
  | _, .pure _ => True
  | _, .liftBind (.act _ _ p) k => p.Lossless ∧ ∀ b, losslessAux (k b)
  | _, .liftBind (.query _ _ _) k => ∀ r, losslessAux (k r)

/-- A program is lossless when every local subinstrument on every branch of its tree is
lossless, including branches that are reached with weight zero. Against a runtime whose steps
are lossless, a lossless program runs to a lossless subinstrument
(`Quantum.QuantumRuntime.lossless_run`). -/
@[expose]
def Lossless (x : QuantumComp spec A B α) : Prop :=
  losslessAux x

/-- Returning a value is lossless. -/
@[simp]
theorem lossless_pure (a : α) : (QuantumComp.pure a : QuantumComp spec A A α).Lossless :=
  trivial

/-- A local subinstrument followed by a continuation is lossless when the subinstrument and
every continuation are. -/
@[simp]
theorem lossless_act_bind_iff (p : SubInstrument A B β) (k : β → QuantumComp spec B C α) :
    ((act p).bind k).Lossless ↔ p.Lossless ∧ ∀ b, (k b).Lossless :=
  Iff.rfl

/-- A call followed by a continuation is lossless when every continuation is. -/
@[simp]
theorem lossless_query_bind_iff (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp spec (QReg.of (spec.Out i × E)) C α) :
    ((query i E ℓ).bind k).Lossless ↔ ∀ r, (k r).Lossless :=
  Iff.rfl

/-- A lossless local subinstrument is a lossless program. -/
theorem lossless_act {p : SubInstrument A B α} (hp : p.Lossless) :
    (act (spec := spec) p).Lossless :=
  ⟨hp, fun _ ↦ trivial⟩

/-- A call is a lossless program. -/
theorem lossless_query (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) :
    (query (spec := spec) i E ℓ).Lossless :=
  fun _ ↦ trivial

/-- Sequencing lossless programs is lossless. -/
theorem Lossless.bind {x : QuantumComp spec A B α} {k : α → QuantumComp spec B C β}
    (hx : x.Lossless) (hk : ∀ a, (k a).Lossless) : (x.bind k).Lossless := by
  refine QuantumComp.inductionOn (motive := fun A B x ↦ ∀ {C : QReg}
    (k : α → QuantumComp spec B C β), x.Lossless → (∀ a, (k a).Lossless) →
      (x.bind k).Lossless) ?_ ?_ ?_ x k hx hk
  · exact fun _ a _ _ _ hk ↦ hk a
  · intro _ _ _ _ p k' ih _ k hx hk
    rw [QuantumComp.bind_assoc, lossless_act_bind_iff] at *
    exact ⟨hx.1, fun b ↦ ih b k (hx.2 b) hk⟩
  · intro _ _ i E ℓ k' ih _ k hx hk
    rw [QuantumComp.bind_assoc, lossless_query_bind_iff] at *
    exact fun r ↦ ih r k (hx r) hk

end QuantumComp

end Quantum
