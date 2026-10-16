/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerComparison

/-!
# Numerical contract for old-oracle offline extraction

`oldOfflineError` is the real-valued function `F` of the repair note FIX (35), with
`oldMerkleOfflineError` converting opened positions to `qs * (d + 1)` raw checks.
The leakage polynomial and invalid-sector term are those of FIX (26b).
Natural subtractions are truncated before casting, and division by six is real division.
Physical parameters have `N > 0` and nonnegative ordinary and extraction masses.

This module specifies the finite error, including its cap, and proves its elementary scalar
properties. It does not assert `OfflineExtractable`: that requires a reachable invalid-norm
bound, collision bound, and a concrete disjoint-database extraction factorization. In particular,
no assertion that arbitrary classical checks preserve population is used. The coefficients
four and eight in FIX (36) belong to the downstream reduction, not to this P4 error function.
-/

public section

namespace Quantum
namespace SaltedMerkle

/-- The leakage sum `T_u` of FIX (35), zero at zero and one total calls. -/
@[expose]
noncomputable def oldLeakagePolynomial (u : ℕ) : ℝ :=
  if 2 ≤ u then (u : ℝ) * (u - 1 : ℕ) * (4 * u - 5 : ℕ) / 6 else 0

/-- The capped fraction of changing labels `a_u` in FIX (35). -/
@[expose]
noncomputable def oldChangingFraction (N u : ℕ) : ℝ :=
  min 1 ((2 * u - 1 : ℕ) / (N : ℝ))

/-- FIX (35): total calls `u`, ordinary mass `w`, extraction mass `e`, and raw checks `q`.
This is a numerical expression, with no claim about the probability of an experiment. -/
@[expose]
noncomputable def oldOfflineError (N u : ℕ) (w e : ℝ) (q : ℕ) : ℝ :=
  min 1 ((Real.sqrt (3 * w * u * (u - 1 : ℕ) / N) + 2 * Real.sqrt ((q : ℝ) / N) +
    2 * Real.sqrt (e * oldLeakagePolynomial u / N) +
    2 * Real.sqrt (u * oldChangingFraction N u)) ^ 2)

/-- The Merkle P4 numerical budget uses `d + 1` hash checks per opened position. -/
@[expose]
noncomputable def oldMerkleOfflineError (N d u : ℕ) (w e : ℝ) (qs : ℕ) : ℝ :=
  oldOfflineError N u w e (qs * (d + 1))

/-- No leakage accumulates before the first call. -/
@[simp] theorem oldLeakagePolynomial_zero : oldLeakagePolynomial 0 = 0 := by
  norm_num [oldLeakagePolynomial]

/-- One call gives a zero leakage polynomial. -/
@[simp] theorem oldLeakagePolynomial_one : oldLeakagePolynomial 1 = 0 := by
  norm_num [oldLeakagePolynomial]

/-- The leakage polynomial is nonnegative, including the two exceptional small budgets. -/
theorem oldLeakagePolynomial_nonneg (u : ℕ) : 0 ≤ oldLeakagePolynomial u := by
  unfold oldLeakagePolynomial
  split_ifs <;> positivity

/-- The finite error is a number in `[0, 1]`. -/
theorem oldOfflineError_mem_Icc (N u : ℕ) (w e : ℝ) (q : ℕ) :
    oldOfflineError N u w e q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (sq_nonneg _), min_le_left _ _⟩

/-- Zero total calls and zero checks give zero error for every mass parameter. -/
@[simp] theorem oldOfflineError_zero (N : ℕ) (w e : ℝ) :
    oldOfflineError N 0 w e 0 = 0 := by
  simp [oldOfflineError]

/-- The Merkle specialization retains the probability cap. -/
theorem oldMerkleOfflineError_mem_Icc (N d u : ℕ) (w e : ℝ) (qs : ℕ) :
    oldMerkleOfflineError N d u w e qs ∈ Set.Icc (0 : ℝ) 1 :=
  oldOfflineError_mem_Icc N u w e (qs * (d + 1))

end SaltedMerkle
end Quantum
