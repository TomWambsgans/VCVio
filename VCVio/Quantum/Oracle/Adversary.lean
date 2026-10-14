/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Basis

/-!
# Query adversaries

A `q`-query adversary on a register `M` is an initial substate, `q + 1` lossless steps, and a
final lossless instrument. Running it against a query step `Q` interleaves the steps with `q`
copies of `Q` and then applies the final instrument:
`step 0, Q, step 1, Q, …, Q, step q, final`.

The adversary does not mention the oracle. `Quantum.QueryAdversary.run` takes the query step as
an argument, so the same adversary runs against the unitary of a sampled function, or against any
other realization of the oracle on its register.

The number of queries is an index of the type. Statements about `q`-query adversaries then
quantify over a type, the steps are a function on `Fin (q + 1)` with no side condition, and
induction on `q` removes the last query with `Quantum.QueryAdversary.dropLast`.

## Main definitions

* `Quantum.interleave Q q s`: the composite `s 0, Q, s 1, …, Q, s q`.
* `Quantum.QueryAdversary M α q`, with `Quantum.QueryAdversary.run`.
* `Quantum.QueryAdversary.stateAfterStep`: the substate after step `i`, on which query `i` acts.
* `Quantum.QueryAdversary.ofClassical`: the adversary that runs a classical deterministic
  algorithm on basis states.

## Main results

* `Quantum.QueryAdversary.outcomeMeasure_run_congr`: two query steps that act in the same way on
  the substates the adversary presents to them give the same outcome measure.
* `Quantum.QueryAdversary.outcomeMeasure_run_ofClassical`: against a query step that permutes
  basis states, a classical adversary reports the output of the classical run with certainty.
-/

public section

open MeasureTheory
open scoped ComplexOrder

namespace Quantum

variable {M : Type*}

section run

variable [Fintype M] {α : Type*} {q : ℕ}

/-! ## Interleaving steps with queries -/

/-- The composite `s 0, Q, s 1, Q, …, Q, s q` of `q + 1` steps interleaved with `q` copies of
the query step `Q`. -/
@[expose]
noncomputable def interleave (Q : SubInstrument M M Unit) :
    (q : ℕ) → (Fin (q + 1) → SubInstrument M M Unit) → SubInstrument M M Unit
  | 0, s => s 0
  | q + 1, s => ((interleave Q q (Fin.init s)).bind fun _ ↦ Q).bind fun _ ↦ s (Fin.last _)

/-- Without queries, the composite is the single step. -/
@[simp]
theorem interleave_zero (Q : SubInstrument M M Unit) (s : Fin 1 → SubInstrument M M Unit) :
    interleave Q 0 s = s 0 :=
  rfl

/-- The composite with one more query: all steps but the last, a query, and the last step. -/
theorem interleave_succ (Q : SubInstrument M M Unit) (s : Fin (q + 2) → SubInstrument M M Unit) :
    interleave Q (q + 1) s =
      ((interleave Q q (Fin.init s)).bind fun _ ↦ Q).bind fun _ ↦ s (Fin.last _) :=
  rfl

/-- The composite with one more query, split at the first query: the first step, a query, and
the composite of the remaining steps. -/
theorem interleave_succ' (Q : SubInstrument M M Unit) (s : Fin (q + 2) → SubInstrument M M Unit) :
    interleave Q (q + 1) s =
      (s 0).bind fun _ ↦ Q.bind fun _ ↦ interleave Q q (Fin.tail s) := by
  induction q with
  | zero => exact SubInstrument.bind_assoc ..
  | succ q ih =>
    rw [interleave_succ, ih, interleave_succ, SubInstrument.bind_assoc,
      SubInstrument.bind_assoc]
    simp only [SubInstrument.bind_assoc]
    rfl

/-- Interleaving lossless steps with a lossless query step is lossless. -/
theorem lossless_interleave {Q : SubInstrument M M Unit} (hQ : Q.Lossless) :
    ∀ {q : ℕ} {s : Fin (q + 1) → SubInstrument M M Unit}, (∀ i, (s i).Lossless) →
      (interleave Q q s).Lossless
  | 0, _, hs => hs 0
  | _ + 1, _, hs =>
    ((lossless_interleave hQ fun i ↦ hs i.castSucc).bind fun _ ↦ hQ).bind fun _ ↦ hs _

/-- The substates after each step of `s 0, Q, s 1, …, Q, s q` run on `ρ`: the entry at `i` is
the substate after step `i`, on which the next query acts. -/
@[expose]
noncomputable def interleavePost (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 1) → SubInstrument M M Unit) : Fin (q + 1) → SubState M :=
  Fin.induction ((s 0).post ρ ()) fun i σ ↦ (s i.succ).post (Q.post σ ()) ()

/-- The substate after step `0` is step `0` applied to the initial substate. -/
@[simp]
theorem interleavePost_zero (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 1) → SubInstrument M M Unit) : interleavePost Q ρ s 0 = (s 0).post ρ () :=
  rfl

/-- The substate after step `i + 1` is the query step and then step `i + 1` applied to the
substate after step `i`. -/
theorem interleavePost_succ (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 1) → SubInstrument M M Unit) (i : Fin q) :
    interleavePost Q ρ s i.succ =
      (s i.succ).post (Q.post (interleavePost Q ρ s i.castSucc) ()) () :=
  Fin.induction_succ ..

/-- Dropping the last step does not change the substates after the earlier steps. -/
theorem interleavePost_init (Q : SubInstrument M M Unit) (ρ : SubState M)
    (s : Fin (q + 2) → SubInstrument M M Unit) (i : Fin (q + 1)) :
    interleavePost Q ρ (Fin.init s) i = interleavePost Q ρ s i.castSucc := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [interleavePost_succ, ih, ← Fin.succ_castSucc, interleavePost_succ]
    rfl

/-- The substate left by the composite is the substate after the last step. -/
theorem post_interleave (Q : SubInstrument M M Unit) (ρ : SubState M) :
    ∀ {q : ℕ} (s : Fin (q + 1) → SubInstrument M M Unit),
      (interleave Q q s).post ρ () = interleavePost Q ρ s (Fin.last q)
  | 0, _ => rfl
  | q + 1, s => by
    rw [interleave_succ, SubInstrument.post_bind_unit, SubInstrument.post_bind_unit,
      post_interleave Q ρ (Fin.init s), interleavePost_init, ← Fin.succ_last,
      interleavePost_succ]

/-! ## Adversaries -/

/-- A `q`-query adversary on the register `M` with outputs in `α`: an initial substate, `q + 1`
lossless steps between which the queries are made, and a final lossless instrument reporting the
output. The steps are arbitrary channels on the register; unitary gates
(`Quantum.SubInstrument.ofIsometry`) are a special case. -/
structure QueryAdversary (M : Type*) [Fintype M] (α : Type*) (q : ℕ) where
  /-- The substate of the register before the first step. -/
  init : SubState M
  /-- The steps: step `0` precedes the first query and step `i + 1` follows query `i`. -/
  step : Fin (q + 1) → SubInstrument M M Unit
  /-- Every step is lossless. -/
  lossless_step : ∀ i, (step i).Lossless
  /-- The final instrument, reporting the output. -/
  final : SubInstrument M M α
  /-- The final instrument is lossless. -/
  lossless_final : final.Lossless

namespace QueryAdversary

variable (adv : QueryAdversary M α q) (Q : SubInstrument M M Unit)

/-- The interaction of the adversary with the query step `Q`, before the final instrument:
`step 0, Q, step 1, …, Q, step q`. -/
@[expose]
noncomputable def body : SubInstrument M M Unit :=
  interleave Q q adv.step

/-- The adversary run against the query step `Q`: the steps interleaved with `q` copies of `Q`,
then the final instrument. -/
@[expose]
noncomputable def run : SubInstrument M M α :=
  (adv.body Q).bind fun _ ↦ adv.final

/-- The substate after step `i` of the run against `Q`, having made `i` queries. For `i < q` it
is the substate on which query `i` acts; for `i = q` the final instrument acts on it. -/
@[expose]
noncomputable def stateAfterStep : Fin (q + 1) → SubState M :=
  interleavePost Q adv.init adv.step

/-- The substate after step `0` is step `0` applied to the initial substate. -/
@[simp]
theorem stateAfterStep_zero : adv.stateAfterStep Q 0 = (adv.step 0).post adv.init () :=
  rfl

/-- The substate after step `i + 1` is the query step and then step `i + 1` applied to the
substate after step `i`. -/
theorem stateAfterStep_succ (i : Fin q) :
    adv.stateAfterStep Q i.succ =
      (adv.step i.succ).post (Q.post (adv.stateAfterStep Q i.castSucc) ()) () :=
  interleavePost_succ ..

/-- The interaction leaves the substate after the last step. -/
theorem post_body : (adv.body Q).post adv.init () = adv.stateAfterStep Q (Fin.last q) :=
  post_interleave Q adv.init adv.step

/-- The outcome measure of a run is that of the final instrument on the substate after the last
step. -/
theorem outcomeMeasure_run [MeasurableSpace α] :
    (adv.run Q).outcomeMeasure adv.init =
      adv.final.outcomeMeasure (adv.stateAfterStep Q (Fin.last q)) := by
  rw [run, SubInstrument.outcomeMeasure_bind_unit, post_body]

variable {Q}

/-- The interaction with a lossless query step is lossless. -/
theorem lossless_body (hQ : Q.Lossless) : (adv.body Q).Lossless :=
  lossless_interleave hQ adv.lossless_step

/-- The run against a lossless query step is lossless. -/
theorem lossless_run (hQ : Q.Lossless) : (adv.run Q).Lossless :=
  (adv.lossless_body hQ).bind fun _ ↦ adv.lossless_final

/-- Against a lossless query step, the adversary reports an output with total weight the trace
of its initial substate. -/
theorem outcomeMeasure_run_apply_univ [MeasurableSpace α] (hQ : Q.Lossless) :
    (adv.run Q).outcomeMeasure adv.init Set.univ = ENNReal.ofReal adv.init.matrix.trace.re :=
  (adv.lossless_run hQ).outcomeMeasure_apply_univ _

/-- Two query steps that act in the same way on each substate the adversary presents to the
first of them lead to the same substates after every step. -/
theorem stateAfterStep_congr {Q' : SubInstrument M M Unit}
    (h : ∀ i : Fin q, Q'.post (adv.stateAfterStep Q i.castSucc) () =
      Q.post (adv.stateAfterStep Q i.castSucc) ()) (i : Fin (q + 1)) :
    adv.stateAfterStep Q' i = adv.stateAfterStep Q i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [stateAfterStep_succ, stateAfterStep_succ, ih, h i]

/-- Two query steps that act in the same way on each substate the adversary presents to the
first of them give the same outcome measure. -/
theorem outcomeMeasure_run_congr [MeasurableSpace α] {Q' : SubInstrument M M Unit}
    (h : ∀ i : Fin q, Q'.post (adv.stateAfterStep Q i.castSucc) () =
      Q.post (adv.stateAfterStep Q i.castSucc) ()) :
    (adv.run Q').outcomeMeasure adv.init = (adv.run Q).outcomeMeasure adv.init := by
  rw [outcomeMeasure_run, outcomeMeasure_run, adv.stateAfterStep_congr h]

/-! ## Removing the last query -/

/-- The adversary without its last query and last step, stopping before the final instrument:
its run is the interaction up to step `q`. -/
@[expose]
noncomputable def dropLast (adv : QueryAdversary M α (q + 1)) : QueryAdversary M Unit q where
  init := adv.init
  step := Fin.init adv.step
  lossless_step i := adv.lossless_step i.castSucc
  final := SubInstrument.pure ()
  lossless_final := SubInstrument.lossless_pure ()

/-- The interaction of an adversary with `q + 1` queries: the interaction of the adversary
without its last query, one query, and the last step. -/
theorem body_succ (adv : QueryAdversary M α (q + 1)) (Q : SubInstrument M M Unit) :
    adv.body Q = ((adv.dropLast.body Q).bind fun _ ↦ Q).bind fun _ ↦ adv.step (Fin.last _) :=
  rfl

/-- The run of the adversary without its last query is its interaction. -/
@[simp]
theorem run_dropLast (adv : QueryAdversary M α (q + 1)) (Q : SubInstrument M M Unit) :
    adv.dropLast.run Q = adv.dropLast.body Q :=
  SubInstrument.bind_pure _

/-- Removing the last query does not change the substates after the earlier steps. -/
theorem stateAfterStep_dropLast (adv : QueryAdversary M α (q + 1)) (Q : SubInstrument M M Unit)
    (i : Fin (q + 1)) : adv.dropLast.stateAfterStep Q i = adv.stateAfterStep Q i.castSucc :=
  interleavePost_init ..

end QueryAdversary

end run

/-! ## Classical adversaries -/

namespace QueryAdversary

section classicalTrajectory

variable {q : ℕ}

/-- The contents of the register after each step of a classical algorithm whose queries rewrite
the register by `π`: start at `m₀`, apply `f 0`, and alternate `π` with the later `f i`. -/
@[expose]
def classicalTrajectory (π : M → M) (m₀ : M) (f : Fin (q + 1) → M → M) : Fin (q + 1) → M :=
  Fin.induction (f 0 m₀) fun i m ↦ f i.succ (π m)

/-- The register after step `0` is `f 0` of the initial contents. -/
@[simp]
theorem classicalTrajectory_zero (π : M → M) (m₀ : M) (f : Fin (q + 1) → M → M) :
    classicalTrajectory π m₀ f 0 = f 0 m₀ :=
  rfl

/-- The register after step `i + 1` is `π` and then `f (i + 1)` of the register after step
`i`. -/
theorem classicalTrajectory_succ (π : M → M) (m₀ : M) (f : Fin (q + 1) → M → M) (i : Fin q) :
    classicalTrajectory π m₀ f i.succ = f i.succ (π (classicalTrajectory π m₀ f i.castSucc)) :=
  Fin.induction_succ ..

end classicalTrajectory

section ofClassical

variable [Fintype M] {α : Type*} {q : ℕ} {Q : SubInstrument M M Unit} [DecidableEq M]

/-- The adversary that runs a classical deterministic algorithm on basis states: it starts in
the basis state at `m₀`, step `i` reads the register in the computational basis and rewrites it
by `f i`, and the final instrument reads the register and reports `g` of it. -/
@[expose]
noncomputable def ofClassical (m₀ : M) (f : Fin (q + 1) → M → M) (g : M → α) :
    QueryAdversary M α q where
  init := SubState.basis m₀
  step i := SubInstrument.classical (f i) fun _ ↦ ()
  lossless_step _ := SubInstrument.lossless_classical _ _
  final := SubInstrument.classical id g
  lossless_final := SubInstrument.lossless_classical _ _

variable {π : M → M} (hQ : ∀ m, Q.post (SubState.basis m) () = SubState.basis (π m))
include hQ

/-- Against a query step that sends the basis state at `m` to the basis state at `π m`, the
register of a classical adversary is in the basis state of the classical trajectory after every
step. -/
theorem stateAfterStep_ofClassical (m₀ : M) (f : Fin (q + 1) → M → M) (g : M → α)
    (i : Fin (q + 1)) :
    (ofClassical m₀ f g).stateAfterStep Q i = SubState.basis (classicalTrajectory π m₀ f i) := by
  induction i using Fin.induction with
  | zero => exact SubInstrument.post_classical_basis _ _
  | succ i ih =>
    rw [stateAfterStep_succ, ih, hQ, classicalTrajectory_succ]
    exact SubInstrument.post_classical_basis _ _

/-- Against a query step that sends the basis state at `m` to the basis state at `π m`, a
classical adversary reports `g` of the last entry of the classical trajectory with certainty. -/
theorem outcomeMeasure_run_ofClassical [MeasurableSpace α] (m₀ : M) (f : Fin (q + 1) → M → M)
    (g : M → α) :
    ((ofClassical m₀ f g).run Q).outcomeMeasure (SubState.basis m₀) =
      Measure.dirac (g (classicalTrajectory π m₀ f (Fin.last q))) := by
  rw [← SubInstrument.outcomeMeasure_classical_basis id g, ← stateAfterStep_ofClassical hQ m₀ f g]
  exact (ofClassical m₀ f g).outcomeMeasure_run Q

end ofClassical

end QueryAdversary

end Quantum
