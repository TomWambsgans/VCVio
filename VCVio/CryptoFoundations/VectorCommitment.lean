/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.Support

/-!
# Vector commitments in the model of one oracle

A vector commitment to messages `m : Fin ℓ → Msg` relative to one classical oracle `X →ₒ Y`
(Chiesa, Di, Hu and Zheng, *How to Prove Post-Quantum Security for Succinct Non-Interactive
Reductions*, ePrint 2025/2166, §3.5, Def 3.5 and Def 3.7) consists of three algorithms:

* `Commit^f(m) → (cm, td)` samples coins and queries the oracle;
* `Open(Q, td) → pf` is oracle-free and deterministic;
* `Check^f(cm, Q, ans, pf) → {0, 1}` queries the oracle and is deterministic given it.

The pair `(Q, ans)` with `ans ∈ Σ^Q` is one partial vector `ans : Fin ℓ → Option Msg` with
`Q = dom ans`; the same type holds the extracted messages `m ∈ (Σ ∪ {⊥})^ℓ` of §7
(ePrint 2025/2166, l.2769).

The check of every vector commitment in §8 of ePrint 2025/2166 has a special form
(Def 8.1 and Thm 8.4 condition 1, l.2960–2969 and l.3031–3034): an oracle-free, non-adaptive
`OutputIO` step lists input-output pairs, and `CheckIO^f` queries every input and compares the
answer with the listed output. `CheckIOForm` records this form together with a bound on the
number of pairs.

## Main definitions

* `PartialVec ℓ Msg`, with `PartialVec.dom`, `PartialVec.Agrees` and `PartialVec.restrict`.
* `VectorCommitment X Y Msg Cm Td Pf ℓ` and `VectorCommitment.PerfectlyComplete`.
* `checkIO io`: query every listed input and compare; `checkIOOn D io`: the same check against a
  partial table `D : X → Option Y`, rejecting at an empty cell.
* `VectorCommitment.CheckIOForm`: `Check` is `OutputIO` followed by `CheckIO`.

## Main results

* `evalWithAnswerFn_checkIO`: against a fixed function `H`, `checkIO io` accepts exactly when
  `H x = y` for every listed pair.
* `checkIOOn_dedup`: removing duplicate pairs does not change acceptance.
-/

public section

open OracleComp OracleSpec

universe u

/-! ## Partial vectors -/

/-- A partial vector of length `ℓ`. It encodes the pair `(Q, ans)` of ePrint 2025/2166,
Def 3.5 (l.1299), as one function with `Q = dom ans`, and an extracted message
`m ∈ (Σ ∪ {⊥})^ℓ` (l.2769), where `none` is `⊥`. -/
abbrev PartialVec (ℓ : ℕ) (Msg : Type u) := Fin ℓ → Option Msg

namespace PartialVec

variable {ℓ : ℕ} {Msg : Type u}

/-- The positions at which a partial vector is defined (`Dom(m)`, l.2876). -/
@[expose]
def dom (v : PartialVec ℓ Msg) : Finset (Fin ℓ) :=
  Finset.univ.filter fun q ↦ (v q).isSome

@[simp]
theorem mem_dom {v : PartialVec ℓ Msg} {q : Fin ℓ} : q ∈ v.dom ↔ (v q).isSome := by
  simp [dom]

/-- `m[Q] = ans` with `Q = dom ans` (l.2893): `m` agrees with `ans` wherever `ans` is defined. -/
@[expose]
def Agrees (m ans : PartialVec ℓ Msg) : Prop :=
  ∀ q a, ans q = some a → m q = some a

instance [DecidableEq Msg] (m ans : PartialVec ℓ Msg) : Decidable (Agrees m ans) :=
  decidable_of_iff (∀ q, ∀ a ∈ ans q, m q = some a) (by simp [Agrees])

/-- The restriction `m[Q]` of a total vector to the positions `Q`. -/
@[expose]
def restrict (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) : PartialVec ℓ Msg :=
  fun q ↦ if q ∈ Q then some (m q) else none

@[simp]
theorem restrict_apply (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) (q : Fin ℓ) :
    restrict m Q q = if q ∈ Q then some (m q) else none :=
  rfl

/-- The restriction to `Q` is defined exactly on `Q`. -/
@[simp]
theorem dom_restrict (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) : (restrict m Q).dom = Q := by
  ext q
  by_cases hq : q ∈ Q <;> simp [hq]

/-- Every partial vector agrees with itself. -/
theorem agrees_refl (m : PartialVec ℓ Msg) : Agrees m m :=
  fun _ _ h ↦ h

end PartialVec

/-! ## Vector commitments -/

/-- A vector commitment to messages `Fin ℓ → Msg` in the model of one oracle `X →ₒ Y`
(ePrint 2025/2166, Def 3.5, l.1291–1310).

`commit` samples coins with `unifSpec` and queries the oracle. `opening` is oracle-free. `check`
makes classical queries and has no coins, so it is deterministic given the oracle. -/
structure VectorCommitment (X Y Msg Cm Td Pf : Type) (ℓ : ℕ) where
  /-- `Commit^f(m) → (cm, td)`. -/
  commit : (Fin ℓ → Msg) → OracleComp (unifSpec + (X →ₒ Y)) (Cm × Td)
  /-- `Open(Q, td) → pf`. -/
  opening : Finset (Fin ℓ) → Td → Pf
  /-- `Check^f(cm, Q, ans, pf) → {0, 1}`, with `Q = dom ans`. -/
  check : Cm → PartialVec ℓ Msg → Pf → OracleComp (X →ₒ Y) Bool

namespace VectorCommitment

variable {X Y Msg Cm Td Pf : Type} {ℓ : ℕ}

/-- The implementation of `unifSpec + (X →ₒ Y)` in `ProbComp` that passes the coins through and
answers every oracle query with the fixed function `H`. -/
@[expose]
def fixedOracleImpl (H : X → Y) : QueryImpl (unifSpec + (X →ₒ Y)) ProbComp :=
  QueryImpl.id' unifSpec + fun x ↦ (pure (H x) : ProbComp Y)

/-- Perfect completeness (ePrint 2025/2166, Def 3.7, l.1316) against every fixed function `H`:
for every message `m`, every query set `Q` and every outcome of `Commit^H(m)`, the honest opening
of `Q` passes `Check^H` on `m[Q]`. Quantifying over all `H` covers every oracle distribution. -/
def PerfectlyComplete (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) : Prop :=
  ∀ (H : X → Y) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)),
    ∀ z ∈ support (simulateQ (fixedOracleImpl H) (vc.commit m)),
      evalWithAnswerFn (QueryImpl.ofFn H)
        (vc.check z.1 (PartialVec.restrict m Q) (vc.opening Q z.2)) = true

end VectorCommitment

/-! ## Input-output checks -/

section CheckIO

variable {X Y : Type} [DecidableEq Y]

/-- One step of `CheckIO`: query `p.1`, compare the answer with `p.2`, and conjoin the result
with the running verdict `acc`. -/
@[expose]
def checkIOStep (acc : Bool) (p : X × Y) : OracleComp (X →ₒ Y) Bool := do
  let y : Y ← (X →ₒ Y).query p.1
  pure (acc && decide (y = p.2))

/-- `CheckIO^f(x, y)` (ePrint 2025/2166, Def 8.1, l.2963): query every listed input `x` and
compare the answer with the listed output `y`. Every query is made, with no short-circuit. -/
@[expose]
def checkIO (io : List (X × Y)) : OracleComp (X →ₒ Y) Bool :=
  io.foldlM checkIOStep true

/-- `CheckIO` against a partial table `D` (l.3043): accept when every listed input has the listed
output in `D`; an empty cell rejects. Stated on `X → Option Y`, the type of
`Quantum.Database X Y`. -/
@[expose]
def checkIOOn (D : X → Option Y) (io : List (X × Y)) : Bool :=
  io.all fun p ↦ decide (D p.1 = some p.2)

@[simp]
theorem evalWithAnswerFn_checkIOStep (H : X → Y) (acc : Bool) (p : X × Y) :
    evalWithAnswerFn (QueryImpl.ofFn H) (checkIOStep acc p) = (acc && decide (H p.1 = p.2)) :=
  rfl

private theorem evalWithAnswerFn_foldlM_checkIOStep (H : X → Y) (io : List (X × Y))
    (acc : Bool) :
    evalWithAnswerFn (QueryImpl.ofFn H) (io.foldlM checkIOStep acc) =
      (acc && io.all fun p ↦ decide (H p.1 = p.2)) := by
  induction io generalizing acc with
  | nil => simp
  | cons p io ih =>
      rw [List.foldlM_cons, evalWithAnswerFn_bind, ih, evalWithAnswerFn_checkIOStep]
      simp [Bool.and_assoc]

/-- Against a fixed function `H`, `checkIO io` accepts exactly when `H x = y` for every listed
pair `(x, y)`. -/
theorem evalWithAnswerFn_checkIO (H : X → Y) (io : List (X × Y)) :
    evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io) = io.all fun p ↦ decide (H p.1 = p.2) := by
  rw [checkIO, evalWithAnswerFn_foldlM_checkIOStep, Bool.true_and]

/-- Against a total table, `checkIOOn` is `checkIO` evaluated at the tabulated function. -/
theorem checkIOOn_some (H : X → Y) (io : List (X × Y)) :
    checkIOOn (fun x ↦ some (H x)) io =
      evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io) := by
  simp [checkIOOn, evalWithAnswerFn_checkIO]

/-- `checkIOOn` accepts exactly when every listed pair is in the table. -/
theorem checkIOOn_eq_true_iff (D : X → Option Y) (io : List (X × Y)) :
    checkIOOn D io = true ↔ ∀ p ∈ io, D p.1 = some p.2 := by
  simp [checkIOOn]

/-- Repeating a check is idempotent: removing duplicate pairs does not change acceptance. -/
theorem checkIOOn_dedup [DecidableEq X] (D : X → Option Y) (io : List (X × Y)) :
    checkIOOn D io.dedup = checkIOOn D io := by
  rw [Bool.eq_iff_iff, checkIOOn_eq_true_iff, checkIOOn_eq_true_iff]
  simp [List.mem_dedup]

/-- Removing duplicate pairs does not change the acceptance of `checkIO` against any fixed
function. -/
theorem evalWithAnswerFn_checkIO_dedup [DecidableEq X] (H : X → Y) (io : List (X × Y)) :
    evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io.dedup) =
      evalWithAnswerFn (QueryImpl.ofFn H) (checkIO io) := by
  rw [← checkIOOn_some, ← checkIOOn_some, checkIOOn_dedup]

end CheckIO

namespace VectorCommitment

variable {X Y Msg Cm Td Pf : Type} {ℓ : ℕ} [DecidableEq Y]

/-- The `CheckIO` form of a check (ePrint 2025/2166, Thm 8.4 condition 1, l.3031–3034): `Check`
runs an oracle-free, non-adaptive `OutputIO` and then `CheckIO`, and `OutputIO` lists at most
`qVC |Q|` pairs. `OutputIO` returns `none` when the proof does not parse; the check then rejects
without a query, the projector `P̂ = 0` of l.2966. The paper's second argument `ℓ` of
`q_VC(qs, ℓ)` (l.3077) is fixed by the scheme and absorbed into `qVC`. -/
structure CheckIOForm (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) where
  /-- `OutputIO(cm, Q, ans, pf) → (x, y)`, or `none` when `pf` does not parse. -/
  outputIO : Cm → PartialVec ℓ Msg → Pf → Option (List (X × Y))
  /-- `Check` is `OutputIO` followed by `CheckIO`. -/
  check_eq : ∀ cm ans pf, vc.check cm ans pf = (outputIO cm ans pf).elim (pure false) checkIO
  /-- The query complexity, as a function of the size of the opened set. -/
  qVC : ℕ → ℕ
  /-- `OutputIO` lists at most `qVC |Q|` pairs. -/
  length_le : ∀ cm ans pf io, outputIO cm ans pf = some io → io.length ≤ qVC ans.dom.card

namespace CheckIOForm

variable {vc : VectorCommitment X Y Msg Cm Td Pf ℓ}

/-- `Check^D` against a partial table `D` (l.3043): reject when the proof does not parse, and
otherwise run `checkIOOn D` on the listed pairs. -/
@[expose]
def checkOn (h : CheckIOForm vc) (D : X → Option Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) : Bool :=
  (h.outputIO cm ans pf).elim false (checkIOOn D)

/-- Against a total table, `checkOn` is `Check` evaluated at the tabulated function. -/
theorem checkOn_some (h : CheckIOForm vc) (H : X → Y) (cm : Cm) (ans : PartialVec ℓ Msg)
    (pf : Pf) :
    h.checkOn (fun x ↦ some (H x)) cm ans pf =
      evalWithAnswerFn (QueryImpl.ofFn H) (vc.check cm ans pf) := by
  rw [h.check_eq, checkOn]
  cases h.outputIO cm ans pf <;> simp [checkIOOn_some]

end CheckIOForm

end VectorCommitment
