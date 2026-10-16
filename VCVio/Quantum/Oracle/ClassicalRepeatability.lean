/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.ClassicalCalls

/-!
# Projective classical answers and exact replay

The sufficient condition for Definition 10.3(2) of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, is an instrument of commuting Hermitian projectors, as in
FIX.md §10, equation (31). All identities below act on matrices, hence on arbitrary
subnormalized states entangled with a reference register. No reachable-state condition
or normalization is used. Ordinary queries commute on a separate call register;
no commutation with extraction is assumed.

A fixed coin tape determines a function from answer prefixes to the next query.
`adaptiveTranscript` records its first finitely many queries. Stopping, inputs and coins
may all be parameters of that function. Replay is branchwise: it retains the probability
of the original transcript and leaves its residual joint state unchanged.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

/-- A projective classical interface of an emulated oracle. The branch equation is for
actual basis calls with an arbitrary held register. Completeness is on the entire private
space, and ordinary commutation includes every port of this oracle. An extraction extension
must therefore be kept outside this structure unless its commutation is proved separately. -/
structure ProjectiveClassicalAnswers {P : Type*} {In : P → QReg}
    (E : EmulatedOracle P In) (X Y : Type) [Fintype Y] [DecidableEq Y] where
  /-- Port and prepared basis input of a classical query. -/
  query : X → Σ p, In p
  /-- Reading of the returned call register. -/
  read : (x : X) → In (query x).1 → Y
  /-- Answer projector on the private register. -/
  A : X → Y → Matrix E.S E.S ℂ
  /-- The actual subnormalized branch, including a reference register. -/
  branch_eq : ∀ (B : QReg) x y,
    (E.toRuntime.run₂ .instruments (QComp.callBasis (query x).1 B (query x).2
      (fun o _ ↦ read x o))).branch y = MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ A x y)
  /-- Each answer projector is Hermitian. -/
  hermitian : ∀ x y, (A x y)ᴴ = A x y
  /-- Answers at the same cell are orthogonal idempotents. -/
  orthogonal : ∀ x z y, A x z * A x y = if z = y then A x y else 0
  /-- The answers resolve the identity, including invalid private sectors. -/
  complete : ∀ x, ∑ y, A x y = 1
  /-- Answer projectors commute across addresses and ports. -/
  commute_cells : ∀ x y x' y', A x y * A x' y' = A x' y' * A x y
  /-- A check commutes with ordinary queries on a separate call register. -/
  commute_ordinary : ∀ p x y,
    E.U p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ A x y) =
      ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ A x y) * E.U p

namespace ProjectiveClassicalAnswers

variable {P : Type*} {In : P → QReg} {E : EmulatedOracle P In}
  {X Y : Type} [Fintype Y] [DecidableEq Y]
  (H : ProjectiveClassicalAnswers E X Y)

/-- The classical-answer branch on a joint reference/private register. -/
noncomputable def branch (B : QReg) (x : X) (y : Y) : MatrixMap (B × E.S) (B × E.S) :=
  MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.A x y)

/-- Repeating a classical call preserves exactly the recorded branch; other answers vanish. -/
theorem repeat_branch (B : QReg) (x : X) (z y : Y) :
    H.branch B x z ∘ₗ H.branch B x y = if z = y then H.branch B x y else 0 := by
  rw [branch, branch, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    H.orthogonal]
  split_ifs <;> simp

/-- Forgetting the answer gives an idempotent channel, including on substates. -/
theorem forget_repeat (B : QReg) (x : X) :
    (∑ y, H.branch B x y) ∘ₗ (∑ y, H.branch B x y) = ∑ y, H.branch B x y := by
  apply LinearMap.ext
  intro ρ
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  have h (z y : Y) : H.branch B x z (H.branch B x y ρ) =
      if z = y then H.branch B x y ρ else 0 := by
    by_cases he : z = y <;> simpa [he] using
      LinearMap.congr_fun (H.repeat_branch B x z y) ρ
  simp_rw [h]
  simp

/-- Product of the projectors prescribed by a classical transcript. -/
noncomputable def projector (tr : List (X × Y)) : Matrix E.S E.S ℂ :=
  (tr.map fun q ↦ H.A q.1 q.2).prod

/-- The empty transcript has identity projector. -/
@[simp] theorem projector_nil : H.projector [] = 1 := by simp [projector]

/-- A transcript starts with its first answer projector. -/
@[simp] theorem projector_cons (q : X × Y) (tr : List (X × Y)) :
    H.projector (q :: tr) = H.A q.1 q.2 * H.projector tr := by simp [projector]

/-- Every answer commutes with every transcript projector. -/
theorem answer_commute_projector (x : X) (y : Y) (tr : List (X × Y)) :
    H.A x y * H.projector tr = H.projector tr * H.A x y := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    simp only [projector_cons]
    rw [← Matrix.mul_assoc, H.commute_cells, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

/-- All transcript projectors are idempotent, including contradictory transcripts. -/
theorem projector_mul_self (tr : List (X × Y)) :
    H.projector tr * H.projector tr = H.projector tr := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    simp only [projector_cons]
    calc
      _ = H.A q.1 q.2 * (H.projector tr * H.A q.1 q.2) * H.projector tr := by
        simp only [Matrix.mul_assoc]
      _ = H.A q.1 q.2 * (H.A q.1 q.2 * H.projector tr) * H.projector tr := by
        rw [← H.answer_commute_projector]
      _ = _ := by rw [← Matrix.mul_assoc, H.orthogonal, ite_eq_left rfl, Matrix.mul_assoc, ih]

/-- The projector of a transcript is Hermitian. -/
theorem projector_hermitian (tr : List (X × Y)) : (H.projector tr)ᴴ = H.projector tr := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    rw [projector_cons, conjTranspose_mul, ih, H.hermitian, ← H.answer_commute_projector]

/-- Joint-state branch for a recorded transcript; no renormalization is performed. -/
noncomputable def transcriptBranch (B : QReg) (tr : List (X × Y)) :
    MatrixMap (B × E.S) (B × E.S) :=
  MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.projector tr)

/-- The empty transcript leaves the joint state unchanged. -/
@[simp] theorem transcriptBranch_nil (B : QReg) :
    H.transcriptBranch B [] = LinearMap.id := by
  simp [transcriptBranch]

/-- The transcript branch is the operational composition in query order. -/
theorem transcriptBranch_cons (B : QReg) (q : X × Y) (tr : List (X × Y)) :
    H.transcriptBranch B (q :: tr) = H.transcriptBranch B tr ∘ₗ H.branch B q.1 q.2 := by
  rw [transcriptBranch, projector_cons, H.answer_commute_projector,
    ← Matrix.one_mul (1 : Matrix B B ℂ), mul_kronecker_mul, MatrixMap.conj_mul]
  rfl

/-- Replaying any recorded transcript leaves its whole subnormalized branch unchanged. -/
theorem replay_transcript (B : QReg) (tr : List (X × Y)) :
    H.transcriptBranch B tr ∘ₗ H.transcriptBranch B tr = H.transcriptBranch B tr := by
  rw [transcriptBranch, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    H.projector_mul_self]

/-- The adaptive transcript determined by a fixed choice of coins, inputs and answer prefix.
The caller chooses a finite stopping prefix; no bound on the policy or its computation is used. -/
def adaptiveTranscript (next : List Y → X) : List Y → List (X × Y)
  | [] => []
  | y :: ys => (next [], y) :: adaptiveTranscript (fun pre ↦ next (y :: pre)) ys

/-- Fixed-coin adaptive replay preserves the original joint branch, including its mass.
The policy may depend on arbitrary fixed public inputs, private coins and prior answers. -/
theorem replay_fixedCoins_transcript {Coins : Type*} (B : QReg)
    (next : Coins → List Y → X) (coins : Coins) (answers : List Y) :
    H.transcriptBranch B (adaptiveTranscript (next coins) answers) ∘ₗ
        H.transcriptBranch B (adaptiveTranscript (next coins) answers) =
      H.transcriptBranch B (adaptiveTranscript (next coins) answers) :=
  H.replay_transcript B _

/-- Two adaptive transcripts of the same length are orthogonal unless every answer agrees.
The query policy is recomputed from the same fixed inputs and coins in both executions. -/
theorem adaptive_projector_mul (next : List Y → X) (ys zs : List Y)
    (hlen : zs.length = ys.length) :
    H.projector (adaptiveTranscript next zs) * H.projector (adaptiveTranscript next ys) =
      if zs = ys then H.projector (adaptiveTranscript next ys) else 0 := by
  induction ys generalizing zs next with
  | nil =>
    have hz : zs = [] := List.length_eq_zero_iff.mp hlen
    subst zs
    simp [adaptiveTranscript]
  | cons y ys ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      have hl : zs.length = ys.length := Nat.succ.inj hlen
      simp only [adaptiveTranscript, projector_cons]
      rw [show (H.A (next []) z *
          H.projector (adaptiveTranscript (fun pre ↦ next (z :: pre)) zs)) *
            (H.A (next []) y *
              H.projector (adaptiveTranscript (fun pre ↦ next (y :: pre)) ys)) =
          (H.A (next []) z * H.A (next []) y) *
            (H.projector (adaptiveTranscript (fun pre ↦ next (z :: pre)) zs) *
              H.projector (adaptiveTranscript (fun pre ↦ next (y :: pre)) ys)) by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc
          (H.projector (adaptiveTranscript (fun pre ↦ next (z :: pre)) zs)),
          ← H.answer_commute_projector]
        simp only [Matrix.mul_assoc]]
      rw [H.orthogonal]
      by_cases hzy : z = y
      · subst z
        rw [ite_eq_left rfl, ih _ _ hl]
        by_cases hzs : zs = ys <;> simp [hzs]
      · simp [hzy]

/-- Replay returns the same adaptive answer transcript and preserves its joint branch.
An alternative answer transcript of the same length has zero residual branch. -/
theorem replay_fixedCoins_answers {Coins : Type*} (B : QReg)
    (next : Coins → List Y → X) (coins : Coins) (ys zs : List Y)
    (hlen : zs.length = ys.length) :
    H.transcriptBranch B (adaptiveTranscript (next coins) zs) ∘ₗ
        H.transcriptBranch B (adaptiveTranscript (next coins) ys) =
      if zs = ys then H.transcriptBranch B (adaptiveTranscript (next coins) ys) else 0 := by
  rw [transcriptBranch, transcriptBranch, ← MatrixMap.conj_mul, ← mul_kronecker_mul,
    Matrix.one_mul, H.adaptive_projector_mul _ _ _ hlen]
  split_ifs <;> simp

/-- An answer already present in a transcript is absorbed by its projector. -/
theorem answer_mul_projector_of_mem (q : X × Y) (tr : List (X × Y)) (hq : q ∈ tr) :
    H.A q.1 q.2 * H.projector tr = H.projector tr := by
  induction tr with
  | nil => simp at hq
  | cons r tr ih =>
    rcases List.mem_cons.mp hq with h | h
    · subst r
      rw [projector_cons, ← Matrix.mul_assoc, H.orthogonal, ite_eq_left rfl]
    · rw [projector_cons, ← Matrix.mul_assoc, H.commute_cells, Matrix.mul_assoc, ih h]

/-- A list prescribing two different answers at one address has zero projector. -/
theorem projector_eq_zero_of_contradiction (tr : List (X × Y)) (x : X) (y z : Y)
    (hy : (x, y) ∈ tr) (hz : (x, z) ∈ tr) (hne : z ≠ y) : H.projector tr = 0 := by
  calc
    H.projector tr = H.A x z * (H.A x y * H.projector tr) := by
      rw [H.answer_mul_projector_of_mem (x, y) tr hy,
        H.answer_mul_projector_of_mem (x, z) tr hz]
    _ = 0 := by rw [← Matrix.mul_assoc, H.orthogonal, ite_eq_right hne, Matrix.zero_mul]

/-- Contradictory transcripts have zero branch on every joint input. -/
theorem transcriptBranch_eq_zero_of_contradiction (B : QReg) (tr : List (X × Y))
    (x : X) (y z : Y) (hy : (x, y) ∈ tr) (hz : (x, z) ∈ tr) (hne : z ≠ y) :
    H.transcriptBranch B tr = 0 := by
  simp [transcriptBranch, H.projector_eq_zero_of_contradiction tr x y z hy hz hne]

/-- Inserting and then forgetting an unused check leaves every commuting retained effect
unchanged. This is an effect identity, not equality of the entire dephased state. -/
theorem sum_unused_check (x : X) (F : Matrix E.S E.S ℂ)
    (hF : ∀ y, H.A x y * F = F * H.A x y) :
    ∑ y, H.A x y * F * H.A x y = F := by
  calc
    _ = ∑ y, F * H.A x y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hF, Matrix.mul_assoc, H.orthogonal, ite_eq_left rfl]
    _ = F := by rw [← Finset.mul_sum, H.complete, Matrix.mul_one]

/-- A retained transcript effect is unaffected by summing any unused check outcome. -/
theorem sum_unused_check_projector (x : X) (tr : List (X × Y)) :
    ∑ y, H.A x y * H.projector tr * H.A x y = H.projector tr :=
  H.sum_unused_check x _ fun y ↦ H.answer_commute_projector x y tr

/-- Ordinary queries may be interposed between a transcript and its replay, on a separate
call register, without changing the retained transcript projector. -/
theorem ordinary_commute_projector (p : P) (tr : List (X × Y)) :
    E.U p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ H.projector tr) =
      ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ H.projector tr) * E.U p := by
  induction tr with
  | nil => simp
  | cons q tr ih =>
    rw [projector_cons, ← Matrix.one_mul (1 : Matrix (In p) (In p) ℂ), mul_kronecker_mul]
    rw [← Matrix.mul_assoc, H.commute_ordinary, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

end ProjectiveClassicalAnswers
end Quantum
