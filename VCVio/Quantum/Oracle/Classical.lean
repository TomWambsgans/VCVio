/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.Quantum.Oracle.Model

/-!
# Classical oracle algorithms in the quantum random-oracle model

A classical algorithm with oracle access to a function `X → Y` is an `OracleComp (X →ₒ Y) α`.
`Quantum.QueryAdversary.ofOracleComp oa q` runs it as a `q`-query adversary on the register
`X × Y × (Fin q → Y)`: the workspace records the answers received so far, and each step reads
the register in the computational basis, stores the last answer, and writes the next query of
`oa` with a cleared response register. The control state of the algorithm is the recorded
answers, from which the remaining computation is recomputed (`OracleComp.feedN`).

## Main results

* `Quantum.QueryAdversary.outcomeMeasure_run_ofOracleComp`: against the oracle unitary of `H`, an
  algorithm making at most `q` queries reports `evalWithAnswerFn (QueryImpl.ofFn H) oa`, its value
  when every query is answered by `H`, with certainty.
* `Quantum.QueryAdversary.qromLaw_ofOracleComp`: its law in the quantum random-oracle model is
  the output measure of the classical experiment that samples `H` uniformly and evaluates `oa`
  against it.
* `Quantum.QueryAdversary.qromLaw_ofOracleComp_eq_randomOracle`: this is also the output measure
  of `oa` under VCVio's lazily sampled, cached random oracle `randomOracle`.
-/

public section

open MeasureTheory OracleSpec
open scoped ENNReal

/-! ## Stepping an oracle computation by its answers -/

namespace OracleComp

variable {X Y α : Type}

/-- The input of the first query of a computation with one oracle, or `default` when it has
returned. -/
@[expose]
def headQueryD [Inhabited X] (oa : OracleComp (X →ₒ Y) α) : X :=
  OracleComp.casesOn oa (fun _ ↦ default) fun t _ ↦ t

/-- The value returned by a computation that makes no query, or `default` when it starts with a
query. -/
@[expose]
def outputD [Inhabited α] (oa : OracleComp (X →ₒ Y) α) : α :=
  OracleComp.casesOn oa (fun a ↦ a) fun _ _ ↦ default

/-- Answer the first query of a computation by `y` and return the remaining computation; a
computation that has returned is unchanged. -/
@[expose]
def feed (oa : OracleComp (X →ₒ Y) α) (y : Y) : OracleComp (X →ₒ Y) α :=
  OracleComp.casesOn oa (fun a ↦ pure a) fun _ k ↦ k y

/-- The computation remaining after the first `n` queries are answered by `t 0, …, t (n - 1)`. -/
@[expose]
def feedN (oa : OracleComp (X →ₒ Y) α) (t : ℕ → Y) : ℕ → OracleComp (X →ₒ Y) α
  | 0 => oa
  | n + 1 => (feedN oa t n).feed (t n)

/-- Answer the first query of a computation by the function `H`. -/
@[expose]
def answerHead [Inhabited X] (H : X → Y) (oa : OracleComp (X →ₒ Y) α) : OracleComp (X →ₒ Y) α :=
  oa.feed (H oa.headQueryD)

@[simp]
theorem headQueryD_pure [Inhabited X] (a : α) :
    (pure a : OracleComp (X →ₒ Y) α).headQueryD = default :=
  rfl

@[simp]
theorem headQueryD_query_bind [Inhabited X] (t : X) (k : Y → OracleComp (X →ₒ Y) α) :
    (liftM ((X →ₒ Y).query t) >>= k).headQueryD = t :=
  rfl

@[simp]
theorem outputD_pure [Inhabited α] (a : α) : (pure a : OracleComp (X →ₒ Y) α).outputD = a :=
  rfl

@[simp]
theorem feed_pure (a : α) (y : Y) : (pure a : OracleComp (X →ₒ Y) α).feed y = pure a :=
  rfl

@[simp]
theorem feed_query_bind (t : X) (k : Y → OracleComp (X →ₒ Y) α) (y : Y) :
    (liftM ((X →ₒ Y).query t) >>= k).feed y = k y :=
  rfl

@[simp]
theorem feedN_zero (oa : OracleComp (X →ₒ Y) α) (t : ℕ → Y) : oa.feedN t 0 = oa :=
  rfl

theorem feedN_succ (oa : OracleComp (X →ₒ Y) α) (t : ℕ → Y) (n : ℕ) :
    oa.feedN t (n + 1) = (oa.feedN t n).feed (t n) :=
  rfl

/-- The computation remaining after `n` answers only depends on the first `n` answers. -/
theorem feedN_congr (oa : OracleComp (X →ₒ Y) α) {t t' : ℕ → Y} {n : ℕ}
    (h : ∀ k < n, t k = t' k) : oa.feedN t n = oa.feedN t' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [feedN_succ, feedN_succ, ih fun k hk ↦ h k (Nat.lt_succ_of_lt hk), h n n.lt_succ_self]

@[simp]
theorem answerHead_pure [Inhabited X] (H : X → Y) (a : α) :
    answerHead H (pure a : OracleComp (X →ₒ Y) α) = pure a :=
  rfl

@[simp]
theorem answerHead_query_bind [Inhabited X] (H : X → Y) (t : X)
    (k : Y → OracleComp (X →ₒ Y) α) :
    answerHead H (liftM ((X →ₒ Y).query t) >>= k) = k (H t) :=
  rfl

/-- Answering the first query by `H`, `n` times, runs a computation with at most `n` queries to
its value against `H`. -/
theorem iterate_answerHead_of_isTotalQueryBound [Inhabited X] (H : X → Y)
    {oa : OracleComp (X →ₒ Y) α} {n : ℕ} (h : IsTotalQueryBound oa n) :
    (answerHead H)^[n] oa = pure (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact Function.iterate_fixed (answerHead_pure H a) n
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.1.ne'
    rw [Function.iterate_succ_apply, answerHead_query_bind,
      ih (H t) (n := n) (by simpa using h.2 (H t)), evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query]
    rfl

end OracleComp

namespace Quantum

namespace QueryAdversary

variable {X Y α : Type} {q : ℕ}

/-! ## The embedding -/

section steps

variable [Inhabited X] [Zero Y]

/-- The answers recorded in the workspace, as a sequence: entry `n` of the workspace for `n < q`,
and zero beyond. -/
@[expose]
def workspaceAnswers (w : Fin q → Y) (n : ℕ) : Y :=
  if h : n < q then w ⟨n, h⟩ else 0

/-- The classical steps of `oa` on the register `X × Y × (Fin q → Y)`. Step `0` writes the first
query of `oa`. Step `i + 1` stores the response register in entry `i` of the workspace, and
writes the next query of the computation that remains after the recorded answers. Every step
clears the response register. -/
@[expose]
def oracleCompStep (oa : OracleComp (X →ₒ Y) α) :
    Fin (q + 1) → X × Y × (Fin q → Y) → X × Y × (Fin q → Y) :=
  Fin.cases (fun m ↦ (oa.headQueryD, 0, m.2.2)) fun i m ↦
    ((oa.feedN (workspaceAnswers (Function.update m.2.2 i m.2.1)) (i + 1)).headQueryD, 0,
      Function.update m.2.2 i m.2.1)

end steps

variable [Inhabited X] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Inhabited α]

/-- The classical oracle algorithm `oa` as a `q`-query adversary on the register
`X × Y × (Fin q → Y)`. It starts in the basis state `(default, 0, 0)`, takes the steps
`Quantum.QueryAdversary.oracleCompStep oa`, and finally reports the value returned by the
computation that remains after the `q` recorded answers, or `default` if that computation has not
returned. -/
@[expose]
noncomputable def ofOracleComp (oa : OracleComp (X →ₒ Y) α) (q : ℕ) :
    QueryAdversary (X × Y × (Fin q → Y)) α q :=
  ofClassical (default, 0, 0) (oracleCompStep oa) fun m ↦
    (oa.feedN (workspaceAnswers m.2.2) q).outputD

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Inhabited α] in
/-- After step `i` of the classical run against `H`, the query register holds the next query of
`oa`, the response register is clear, and the workspace records the answers of `H` to the first
`i` queries. -/
private theorem classicalTrajectory_oracleCompStep (oa : OracleComp (X →ₒ Y) α) (H : X → Y)
    (i : Fin (q + 1)) :
    (classicalTrajectory (oracleEquiv H) (default, 0, 0) (oracleCompStep oa) i).1 =
        ((OracleComp.answerHead H)^[i] oa).headQueryD ∧
      (classicalTrajectory (oracleEquiv H) (default, 0, 0) (oracleCompStep oa) i).2.1 = 0 ∧
      oa.feedN (workspaceAnswers
        (classicalTrajectory (oracleEquiv H) (default, 0, 0) (oracleCompStep oa) i).2.2) i =
        (OracleComp.answerHead H)^[i] oa := by
  induction i using Fin.induction with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ i ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    rw [classicalTrajectory_succ]
    generalize classicalTrajectory (oracleEquiv H) (default, 0, 0) (oracleCompStep oa)
      i.castSucc = m at h₁ h₂ h₃
    rw [Fin.val_castSucc] at h₁ h₃
    have key : oa.feedN (workspaceAnswers (Function.update m.2.2 i (m.2.1 + H m.1))) (i + 1) =
        (OracleComp.answerHead H)^[i + 1] oa := by
      rw [OracleComp.feedN_succ, Function.iterate_succ_apply', ← h₃,
        OracleComp.feedN_congr oa (t' := workspaceAnswers m.2.2) fun k hk ↦ ?_]
      · simp [OracleComp.answerHead, h₃, ← h₁, workspaceAnswers, h₂]
      · rw [workspaceAnswers, workspaceAnswers]
        split_ifs with hkq
        · exact Function.update_of_ne (fun h ↦ hk.ne (congrArg Fin.val h)) _ _
        · rfl
    exact ⟨congrArg OracleComp.headQueryD key, rfl, key⟩

/-- Against the oracle unitary of `H`, a classical algorithm making at most `q` queries reports
its value against `H` with certainty. -/
theorem outcomeMeasure_run_ofOracleComp [MeasurableSpace α] {oa : OracleComp (X →ₒ Y) α}
    (h : OracleComp.IsTotalQueryBound oa q) (H : X → Y) :
    ((ofOracleComp oa q).run (oracleQuery H)).outcomeMeasure (ofOracleComp oa q).init =
      Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  refine (outcomeMeasure_run_ofClassical (π := oracleEquiv H) (post_oracleQuery_basis H)
    (default, 0, 0) (oracleCompStep oa) _).trans ?_
  have key := (classicalTrajectory_oracleCompStep oa H (Fin.last q)).2.2
  rw [Fin.val_last] at key
  rw [key, OracleComp.iterate_answerHead_of_isTotalQueryBound H h, OracleComp.outputD_pure]

/-! ## Agreement with the classical random-oracle model -/

variable [SampleableType (X → Y)]

/-- **The quantum random-oracle model agrees with the classical one on classical algorithms.**
The law, in the quantum random-oracle model, of a classical algorithm making at most `q` queries
is the output measure of the classical experiment that samples a function `H : X → Y` uniformly
and evaluates the algorithm with every query answered by `H`. -/
theorem qromLaw_ofOracleComp [MeasurableSpace α] {oa : OracleComp (X →ₒ Y) α}
    (h : OracleComp.IsTotalQueryBound oa q) :
    (ofOracleComp oa q).qromLaw =
      𝒟[do let H ← $ᵗ (X → Y); pure (evalWithAnswerFn (QueryImpl.ofFn H) oa)] := by
  let : MeasurableSpace (X → Y) := ⊤
  rw [evalDist_bind_of_discrete, qromLaw, outcomeLaw]
  simp only [outcomeMeasure_run_ofOracleComp h, evalDist_pure]

/-- The law, in the quantum random-oracle model, of a classical algorithm making at most `q`
queries is its output measure under the lazily sampled, cached random oracle. -/
theorem qromLaw_ofOracleComp_eq_randomOracle [SampleableType Y] [MeasurableSpace α]
    {oa : OracleComp (X →ₒ Y) α} (h : OracleComp.IsTotalQueryBound oa q) :
    (ofOracleComp oa q).qromLaw = 𝒟[(simulateQ randomOracle oa).run' ∅] := by
  rw [qromLaw_ofOracleComp h, OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable]

end QueryAdversary

end Quantum
