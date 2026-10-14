/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Classical
public import VCVio.Quantum.Oracle.Comb

/-!
# Quantum oracle regression tests

Oracles `Fin 2 → Fin 2`, queried on the register `Fin 2 × Fin 2`.

* **Deutsch's algorithm**, as a one-query comb, reports `H 0 + H 1` with certainty. Its program
  (`Quantum.QuantumComb.toComp`) runs as the comb does (Proposition 1), with one call.
* **Classical algorithms.** The program of the algorithm that queries `0` reports `H 0`; its law
  in the quantum random-oracle model is its law under the lazily sampled random oracle, with no
  query bound. The adaptive algorithm that queries `H 0` next reports `H (H 0)`. Running the
  program of a sequenced algorithm is sequencing the runs (`Quantum.QuantumRuntime.run_bind`).
* **An adaptive program** measures a bit and calls the oracle only when it reads `1`: it has
  budget one, and not budget zero.
* **An ancilla** is allocated, carried through a call as the remainder of the register, and
  discarded.
* **Two ports.** A program calling each port once has budget one per port, and not budget one
  on one port alone. A program that calls only one port runs in the same way whatever the other
  port does.
* **A stateful runtime.** The counting runtime of the design note's Proposition 3 counts the
  calls in its private register. A program that flips a coin and calls twice on heads and once
  on tails leaves the counter at `2` or `1` according to the coin; a comb with a fixed number of
  slots cannot.
* **Guessing without queries.** A lossless program with budget zero guesses a point of a
  uniformly sampled oracle with probability `1 / 2`.
-/

public section

open Quantum Matrix MeasureTheory OracleSpec
open scoped ComplexOrder ENNReal Kronecker

namespace VCVioTest.QuantumOracle

/-- The random-oracle signature for oracles `Fin 2 → Fin 2`. -/
abbrev qrom2 : QuantumOracleSpec :=
  qromSpec (Fin 2) (Fin 2)

/-! ## Deutsch's algorithm -/

/-- The register of Deutsch's algorithm: one query qubit and one response qubit. -/
abbrev Reg : Type := Fin 2 × Fin 2

/-- The sign `(-1) ^ y` of a bit. -/
def sgn (y : Fin 2) : ℂ :=
  if y = 0 then 1 else -1

/-- The amplitudes of the state `|+⟩|-⟩`. -/
noncomputable def amp : Reg → ℂ :=
  fun m ↦ sgn m.2 / 2

/-- The projector onto `|+⟩` (for `b = 0`) or `|-⟩` (for `b = 1`) of the query qubit. -/
noncomputable def proj (b : Fin 2) : Matrix Reg Reg ℂ :=
  Matrix.of fun m m' ↦ if m.2 = m'.2 then sgn (b * (m.1 + m'.1)) / 2 else 0

theorem eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The projectors onto `|+⟩` and `|-⟩` satisfy the completeness relation. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ b, (proj b)ᴴ * proj b = 1 := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rcases eq_zero_or_one x with rfl | rfl <;> rcases eq_zero_or_one y with rfl | rfl <;>
    rcases eq_zero_or_one x' with rfl | rfl <;> rcases eq_zero_or_one y' with rfl | rfl <;>
    norm_num [Fin.sum_univ_two, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, proj,
      sgn, map_ofNat]

/-- The state `|+⟩|-⟩`. -/
noncomputable def plusMinus : SubState Reg where
  matrix := vecMulVec amp (star amp)
  posSemidef := Matrix.posSemidef_vecMulVec_self_star amp
  trace_re_le_one := by
    norm_num [Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, amp, sgn]

/-- Deutsch's algorithm: start in `|+⟩|-⟩`, query once, and measure the query qubit in the
`|±⟩` basis. -/
noncomputable def deutsch : QuantumComb Reg (Fin 2) 1 where
  init := plusMinus
  step _ := SubInstrument.pure ()
  lossless_step _ := SubInstrument.lossless_pure ()
  final := SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj
  lossless_final := SubInstrument.lossless_ofKraus _ _

/-- The weight of a Kraus branch on a pure state is the squared norm of the image vector. -/
theorem trace_conj_vecMulVec {A B : Type} [Fintype A] [Fintype B] (K : Matrix B A ℂ)
    (v : A → ℂ) :
    (MatrixMap.conj K (vecMulVec v (star v))).trace = ∑ i, (K *ᵥ v) i * star ((K *ᵥ v) i) := by
  rw [MatrixMap.conj_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
    Matrix.trace_vecMulVec]
  rfl

/-- After the query, the measurement reports `H 0 + H 1` with weight one. -/
theorem trace_conj_proj (H : Fin 2 → Fin 2) (b : Fin 2) :
    (MatrixMap.conj (proj b)
      (MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)))).trace =
      if b = H 0 + H 1 then 1 else 0 := by
  have h : MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) =
      vecMulVec (fun m ↦ amp ((oracleEquiv H).symm m))
        (star fun m ↦ amp ((oracleEquiv H).symm m)) := by
    rw [oracleUnitary, conj_basisMatrix_equiv]
    rfl
  rw [h, trace_conj_vecMulVec]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    rcases eq_zero_or_one b with rfl | rfl <;>
    norm_num [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, proj, amp, sgn,
      oracleEquiv_symm_apply, h0, h1]

/-- Deutsch's algorithm reports `H 0 + H 1` with certainty. -/
theorem outcomeMeasure_deutsch (H : Fin 2 → Fin 2) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init = Measure.dirac (H 0 + H 1) := by
  rw [QuantumComb.outcomeMeasure_run, show Fin.last 1 = (0 : Fin 1).succ from rfl,
    QuantumComb.stateAfterStep_succ]
  change deutsch.final.outcomeMeasure ((SubInstrument.pure ()).post
    ((oracleQuery H).post ((SubInstrument.pure ()).post plusMinus ()) ()) ()) = _
  rw [SubInstrument.post_pure_self, SubInstrument.post_pure_self,
    SubInstrument.outcomeMeasure_eq_sum_univ, Fin.sum_univ_two]
  have h : ∀ b, (deutsch.final.branch b ((oracleQuery H).post plusMinus ()).matrix).trace =
      if b = H 0 + H 1 then 1 else 0 := fun b ↦ by
    have h₁ : ((oracleQuery H).post plusMinus ()).matrix =
        MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) := by
      simp [MatrixMap.conj_apply, plusMinus]
    rw [h₁]
    change ((SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj).branch b _).trace = _
    rw [SubInstrument.branch_ofKraus_apply]
    exact trace_conj_proj H b
  rw [h, h]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [h0, h1]

/-- On a constant oracle, Deutsch's algorithm reports `0` with certainty. -/
example (H : Fin 2 → Fin 2) (h : H 0 = H 1) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init {0} = 1 := by
  rcases eq_zero_or_one (H 1) with h1 | h1 <;> simp [outcomeMeasure_deutsch, h, h1]

/-- On a balanced oracle, Deutsch's algorithm reports `1` with certainty. -/
example (H : Fin 2 → Fin 2) (h : H 0 ≠ H 1) :
    (deutsch.run (oracleQuery H)).outcomeMeasure deutsch.init {1} = 1 := by
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [outcomeMeasure_deutsch, h0, h1] at h ⊢

/-- Deutsch's algorithm as a program over the random-oracle signature: its call goes to the
whole register, with the trivial remainder. -/
noncomputable def deutschComp : QuantumComp qrom2 (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  deutsch.toComp () (QReg.of Unit) (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)

/-- **Proposition 1** for Deutsch's algorithm: against the oracle runtime, the program runs as the
comb, framed by the runtime register, against the runtime's query step. -/
example (H : Fin 2 → Fin 2) :
    (xorRuntime H).run deutschComp =
      (deutsch.frame (xorRuntime H).D (xorRuntime H).init).run
        ((xorRuntime H).combQuery () (QReg.of Unit) (Equiv.prodPUnit Reg).symm
          (Equiv.prodPUnit Reg)) :=
  QuantumComb.run_toComp ..

/-- The program of Deutsch's algorithm makes one call, and is lossless. -/
example : deutschComp.IsQueryBound (Pi.single (() : qrom2.Port) 1) ∧ deutschComp.Lossless :=
  ⟨deutsch.isQueryBound_toComp (spec := qrom2) () _ _ _,
    deutsch.lossless_toComp (spec := qrom2) () _ _ _⟩

/-! ## Classical algorithms -/

/-- The classical algorithm that queries the oracle at `0` and returns the answer. -/
def queryZero : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) :=
  liftM ((Fin 2 →ₒ Fin 2).query 0)

/-- The algorithm makes at most one query. -/
theorem isTotalQueryBound_queryZero : OracleComp.IsTotalQueryBound queryZero 1 := by
  rw [queryZero, ← bind_pure (liftM _), OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- Against the oracle unitary of `H`, the program of the algorithm reports `H 0` with
certainty. -/
example (H : Fin 2 → Fin 2) :
    (xorRuntime H).outcomeLaw queryZero.toQuantum (SubState.basis ()) = Measure.dirac (H 0) :=
  outcomeLaw_xorRuntime_toQuantum H queryZero

/-- The program makes one call. -/
example : queryZero.toQuantum.IsQueryBound fun _ ↦ 1 :=
  OracleComp.isQueryBound_toQuantum isTotalQueryBound_queryZero

/-- The law of the program in the quantum random-oracle model is the law of the algorithm under
the lazily sampled random oracle; no query bound is used. -/
example :
    qromLaw queryZero.toQuantum (SubState.basis ()) =
      𝒟[(simulateQ randomOracle queryZero).run' ∅] :=
  qromLaw_toQuantum_eq_randomOracle queryZero

/-- The adaptive algorithm that queries `0`, and then queries the answer. -/
def queryTwice : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) := do
  let y ← liftM ((Fin 2 →ₒ Fin 2).query 0)
  liftM ((Fin 2 →ₒ Fin 2).query y)

/-- Its program, whose second call depends on the measured result of the first, reports
`H (H 0)` with certainty. -/
example (H : Fin 2 → Fin 2) :
    (xorRuntime H).outcomeLaw queryTwice.toQuantum (SubState.basis ()) =
      Measure.dirac (H (H 0)) :=
  outcomeLaw_xorRuntime_toQuantum H queryTwice

/-- Running the program of a sequenced algorithm is sequencing the runs of the programs. -/
example {α β : Type} (H : Fin 2 → Fin 2) (oa : OracleComp (Fin 2 →ₒ Fin 2) α)
    (f : α → OracleComp (Fin 2 →ₒ Fin 2) β) :
    (xorRuntime H).run (oa >>= f).toQuantum =
      ((xorRuntime H).run oa.toQuantum).bind fun a ↦ (xorRuntime H).run (f a).toQuantum := by
  rw [OracleComp.toQuantum, simulateQ_bind]
  exact QuantumRuntime.run_bind _ _ _

/-! ## An adaptive program -/

/-- Measure the query bit; on `1`, call the oracle and return to the register `Fin 2 × Fin 2`;
then return the bit. The number of calls depends on the measured outcome. -/
noncomputable def callIfOne : QuantumComp qrom2 (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  (QuantumComp.act (A := QReg.of Reg) (B := QReg.of Reg)
      (SubInstrument.classical id fun m : Reg ↦ m.1)).bind fun b ↦
    if b = 1 then
      ((QuantumComp.query () (QReg.of Unit) (Equiv.prodPUnit Reg).symm).bind fun _ ↦
        QuantumComp.act (B := QReg.of Reg) (SubInstrument.relabel (Equiv.prodPUnit Reg))).bind
          fun _ ↦ QuantumComp.pure b
    else QuantumComp.pure b

/-- The adaptive program makes at most one call on every path. -/
example : callIfOne.IsQueryBound fun _ ↦ 1 := by
  rw [callIfOne, QuantumComp.isQueryBound_act_bind_iff]
  intro b
  split_ifs
  · refine ((((QuantumComp.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos).bind
      fun _ ↦ QuantumComp.isQueryBound_act _ 0).bind (b₂ := 0)
        fun _ ↦ QuantumComp.isQueryBound_pure _ _).mono fun _ ↦ ?_
    simp
  · exact QuantumComp.isQueryBound_pure _ _

/-- The adaptive program calls the oracle on the path where it reads `1`. -/
example : ¬ callIfOne.IsQueryBound 0 := by
  intro h
  rw [callIfOne, QuantumComp.isQueryBound_act_bind_iff] at h
  have h₁ := h 1
  simp only [↓reduceIte] at h₁
  rw [QuantumComp.bind_assoc] at h₁
  exact Nat.lt_irrefl 0 (QuantumComp.IsQueryBound.of_query_bind h₁).1

/-! ## Allocating and discarding an ancilla -/

/-- Allocate an ancilla qubit in `|0⟩`: the isometry `|a⟩ ↦ |a, 0⟩`. -/
noncomputable def alloc (A : Type) [Fintype A] [DecidableEq A] : SubInstrument A (A × Fin 2) Unit :=
  SubInstrument.ofIsometry (basisMatrix fun a : A ↦ (a, (0 : Fin 2)))
    (conjTranspose_basisMatrix_mul_self fun _ _ h ↦ congrArg Prod.fst h)

/-- The Kraus operators `1 ⊗ ⟨r|` of the partial trace over an ancilla qubit. -/
def discardKraus (A : Type) [DecidableEq A] (r : Fin 2) : Matrix A (A × Fin 2) ℂ :=
  Matrix.of fun a p ↦ if p = (a, r) then 1 else 0

/-- The Kraus operators of the partial trace satisfy the completeness relation. -/
theorem sum_discardKraus (A : Type) [Fintype A] [DecidableEq A] :
    ∑ r, (discardKraus A r)ᴴ * discardKraus A r = 1 := by
  ext ⟨a, s⟩ ⟨a', s'⟩
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, discardKraus, Matrix.of_apply,
    Prod.mk.injEq, apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single s (fun r _ hr ↦ by simp [Ne.symm hr]) (by simp),
    Finset.sum_eq_single a (fun x _ hx ↦ by simp [Ne.symm hx]) (by simp)]
  by_cases ha : a' = a
  · subst ha
    by_cases hs : s' = s
    · subst hs
      simp
    · simp [hs, Ne.symm hs]
  · simp [ha, Ne.symm ha]

/-- Discard an ancilla qubit: the partial trace over it. -/
noncomputable def discard (A : Type) [Fintype A] [DecidableEq A] :
    SubInstrument (A × Fin 2) A Unit :=
  (SubInstrument.ofKraus (discardKraus A) (sum_discardKraus A)).map fun _ ↦ ()

/-- Allocate an ancilla, call the oracle with the ancilla as the remainder of the register, and
discard the ancilla. -/
noncomputable def queryWithAncilla : QuantumComp qrom2 (QReg.of Reg) (QReg.of Reg) Unit :=
  (QuantumComp.act (B := QReg.of (Reg × Fin 2)) (alloc Reg)).bind fun _ ↦
    (QuantumComp.query () (QReg.of (Fin 2)) (Equiv.refl (Reg × Fin 2))).bind fun _ ↦
      QuantumComp.act (B := QReg.of Reg) (discard Reg)

/-- The program with an ancilla is lossless and makes one call. -/
theorem lossless_queryWithAncilla : queryWithAncilla.Lossless :=
  (QuantumComp.lossless_act (SubInstrument.lossless_ofIsometry _ _)).bind fun _ ↦
    (QuantumComp.lossless_query _ _ _).bind fun _ ↦
      QuantumComp.lossless_act ((SubInstrument.lossless_ofKraus _ _).map _)

example : queryWithAncilla.IsQueryBound fun _ ↦ 1 := by
  rw [queryWithAncilla, QuantumComp.isQueryBound_act_bind_iff]
  intro _
  exact (((QuantumComp.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos).bind
    fun _ ↦ QuantumComp.isQueryBound_act _ 0).mono fun _ ↦ le_of_eq (add_zero _)

/-- Against the oracle unitary, the program with an ancilla keeps the trace of its input. -/
example (H : Fin 2 → Fin 2) (ρ : SubState (QReg.of Reg)) :
    (xorRuntime H).outcomeLaw queryWithAncilla ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [(xorRuntime H).outcomeLaw_apply_univ_of_lossless
    (lossless_run_xorRuntime lossless_queryWithAncilla H), trace_re_xorRuntime_init, mul_one]

/-! ## Two ports -/

/-- Two oracles `Fin 2 → Fin 2`, one on each port. -/
@[expose, reducible]
def twoSpec : QuantumOracleSpec where
  Port := Bool
  In _ := QReg.of Reg
  Out _ := QReg.of Reg
  Result _ := Unit

/-- The runtime that answers port `true` with the oracle unitary of `H` and port `false` with that
of `G`. -/
@[expose]
noncomputable def twoXor (H G : Fin 2 → Fin 2) : QuantumRuntime twoSpec where
  D := QReg.of Unit
  init := SubState.basis ()
  step b := (oracleQuery (cond b H G)).frame Unit

/-- Call port `true`, then port `false`. -/
noncomputable def callBoth :
    QuantumComp twoSpec (QReg.of Reg) (QReg.of (Reg × Unit)) Unit :=
  (QuantumComp.query true (QReg.of Unit) (Equiv.prodPUnit Reg).symm).bind fun _ ↦
    QuantumComp.query false (QReg.of Unit) (Equiv.refl (Reg × Unit))

/-- The program calls each port once. -/
example : callBoth.IsQueryBound fun _ ↦ 1 := by
  refine (QuantumComp.IsQueryBound.bind (spec := twoSpec) (b₁ := Pi.single true 1)
    (b₂ := Pi.single false 1)
    ((QuantumComp.isQueryBound_query_iff _ _ _ _).mpr (by simp))
    fun _ ↦ (QuantumComp.isQueryBound_query_iff _ _ _ _).mpr (by simp)).mono fun b ↦ ?_
  cases b <;> simp

/-- A budget on port `true` alone does not cover the call of port `false`. -/
example : ¬ callBoth.IsQueryBound (Pi.single (true : twoSpec.Port) 1) := by
  intro h
  have h₁ := (QuantumComp.IsQueryBound.of_query_bind h).2 ()
  rw [QuantumComp.isQueryBound_query_iff] at h₁
  simp at h₁

/-- Call port `true` only. -/
noncomputable def callTrue : QuantumComp twoSpec (QReg.of Reg) (QReg.of (Reg × Unit)) Unit :=
  QuantumComp.query true (QReg.of Unit) (Equiv.prodPUnit Reg).symm

/-- A program that calls only port `true` runs in the same way whatever port `false` does. -/
example (H G G' : Fin 2 → Fin 2) : (twoXor H G).run callTrue = (twoXor H G').run callTrue := by
  refine QuantumRuntime.run_congr_of_isQueryBound (D := QReg.of Unit)
    (σ₁ := SubState.basis ()) (σ₂ := SubState.basis ()) (s₁ := (twoXor H G).step)
    (s₂ := (twoXor H G').step) (b := Pi.single (true : twoSpec.Port) 1)
    ((QuantumComp.isQueryBound_query_iff _ _ _ _).mpr (by simp)) fun i hi ↦ ?_
  cases i
  · simp at hi
  · rfl

/-! ## A stateful runtime -/

/-- One port with trivial registers: a call only acts on the runtime's private register. -/
@[expose, reducible]
def countSpec : QuantumOracleSpec where
  Port := Unit
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Unit

/-- Count one more call, saturating at `2`. -/
@[expose]
def tick (d : Fin 3) : Fin 3 :=
  if d = 2 then 2 else d + 1

/-- **The counting runtime.** Its private register `Fin 3` starts at `0` and counts the calls,
saturating at `2`. It is reducible, so that its register unfolds to `Fin 3` when rewriting. -/
@[expose, reducible]
noncomputable def countRuntime : QuantumRuntime countSpec where
  D := QReg.of (Fin 3)
  init := SubState.basis 0
  step _ := SubInstrument.classical (fun m : Unit × Fin 3 ↦ ((), tick m.2)) fun _ ↦ ()

/-- A call of the counting runtime on a basis state advances the counter. -/
theorem countRuntime_step_branch_single (d : Fin 3) :
    (countRuntime.step ()).branch () (Matrix.single ((), d) ((), d) 1) =
      Matrix.single ((), tick d) ((), tick d) 1 :=
  (SubInstrument.branch_classical_basis (fun m : Unit × Fin 3 ↦ ((), tick m.2)) (fun _ ↦ ())
    ((), d) ()).trans (by simp)

/-- Measure a coin; call twice on heads (`1`) and once on tails (`0`); return the coin. -/
@[expose]
noncomputable def coinProg :
    QuantumComp countSpec (QReg.of (Fin 2)) (QReg.of (Unit × Fin 2)) (Fin 2) :=
  (QuantumComp.act (A := QReg.of (Fin 2)) (B := QReg.of (Fin 2))
      (SubInstrument.classical id id)).bind fun b ↦
    (QuantumComp.query () (QReg.of (Fin 2)) (Equiv.punitProd (Fin 2)).symm).bind fun _ ↦
      if b = 1 then
        (QuantumComp.query () (QReg.of (Fin 2)) (Equiv.refl (Unit × Fin 2))).bind fun _ ↦
          QuantumComp.pure b
      else QuantumComp.pure b

/-- The coin program makes at most two calls on every path. -/
example : coinProg.IsQueryBound fun _ ↦ 2 := by
  rw [coinProg, QuantumComp.isQueryBound_act_bind_iff]
  intro b
  refine (QuantumComp.IsQueryBound.bind (b₁ := fun _ ↦ 1) (b₂ := fun _ ↦ 1)
    ((QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos) fun _ ↦ ?_).mono
      fun _ ↦ le_refl _
  split_ifs
  · exact ((QuantumComp.isQueryBound_query_iff _ _ _ _).mpr Nat.one_pos).bind (b₂ := 0)
      (fun _ ↦ QuantumComp.isQueryBound_pure _ _) |>.mono fun _ ↦ le_of_eq (add_zero _)
  · exact QuantumComp.isQueryBound_pure _ _

/-- The run of the coin program on a basis state `|b, d⟩`. -/
theorem run_coinProg_branch_single (b c : Fin 2) (d : Fin 3) :
    (countRuntime.run coinProg).branch c (Matrix.single (b, d) (b, d) 1) =
      if b = c then
        Matrix.single (((), b), if b = 1 then tick (tick d) else tick d)
          (((), b), if b = 1 then tick (tick d) else tick d) 1
      else 0 := by
  rw [coinProg, QuantumRuntime.run_act_bind, SubInstrument.branch_bind_apply_univ,
    LinearMap.sum_apply, Finset.sum_eq_single b (fun b' _ hb' ↦ ?_) (by simp),
    LinearMap.comp_apply, SubInstrument.branch_frame_single, SubInstrument.branch_classical_basis]
  · simp only [id, ↓reduceIte, Matrix.single_kronecker_single, one_mul]
    rw [QuantumRuntime.run_query_bind, SubInstrument.branch_bind_unit, LinearMap.comp_apply,
      QuantumRuntime.queryStep_branch_single, Equiv.punitProd_symm_apply,
      countRuntime_step_branch_single, Matrix.single_kronecker_single, one_mul,
      SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
      QuantumRuntime.queryEquivOut_apply]
    rcases eq_zero_or_one b with rfl | rfl
    · simp [SubInstrument.branch_pure, Pi.single_apply]
      split_ifs <;> simp_all
    · simp only [↓reduceIte]
      rw [QuantumRuntime.run_query_bind, SubInstrument.branch_bind_unit, LinearMap.comp_apply,
        QuantumRuntime.queryStep_branch_single, Equiv.refl_apply,
        countRuntime_step_branch_single, Matrix.single_kronecker_single, one_mul,
        SubInstrument.branch_relabel, conj_basisMatrix_equiv_single,
        QuantumRuntime.queryEquivOut_apply]
      simp [SubInstrument.branch_pure, Pi.single_apply]
      split_ifs <;> simp_all
  · rw [LinearMap.comp_apply, SubInstrument.branch_frame_single,
      SubInstrument.branch_classical_basis]
    simp [Ne.symm hb']

/-- **Proposition 3.** On heads the counting runtime ends at `2`, on tails at `1`: the final
state of its private register depends on the path of the program. A comb with a fixed number of
slots calls the same number of times on every path. -/
example :
    countRuntime.jointPost coinProg (SubState.basis 1) 1 =
        SubState.basis (((), 1), (2 : Fin 3)) ∧
      countRuntime.jointPost coinProg (SubState.basis 0) 0 =
        SubState.basis (((), 0), (1 : Fin 3)) := by
  constructor <;>
  · refine SubState.ext ?_
    rw [QuantumRuntime.matrix_jointPost, SubState.matrix_basis, SubState.matrix_basis,
      SubState.matrix_basis, Matrix.single_kronecker_single, one_mul, run_coinProg_branch_single]
    rfl

/-! ## Guessing without queries -/

/-- A lossless program with budget zero, started in a state of trace one, guesses a point of the
oracle with probability `1 / 2`. -/
example {A B : QReg} (x : QuantumComp qrom2 A B (Fin 2 × Fin 2)) (hx : x.IsQueryBound 0)
    (hl : x.Lossless) {ρ : SubState A} (h : ρ.matrix.trace = 1) :
    qromLawWith x ρ (fun H a ↦ a.2 = H a.1) {True} = 2⁻¹ := by
  simpa using qromLawWith_guess_zero_of_trace_eq_one hx hl h

end VCVioTest.QuantumOracle
