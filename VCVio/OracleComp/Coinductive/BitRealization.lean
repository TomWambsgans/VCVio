/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.Responder
public import VCVio.OracleComp.Coinductive.Machine
public import VCVio.EvalDist.MachineMeasure
public import PolyFun.PFunctor.Dynamical.DynComputation.IO

/-!
# Fair-bit realizations of probabilistic services

A realization supplies executable machines and proves their returned-output measures equal
the service's joint answer/state kernels. Unlike a finite `ProbComp` presentation, a machine
may require an unbounded number of random bits. A probability answer kernel certifies almost
sure return through the equality of total mass; a subprobability kernel can describe genuine
divergence. The IO adapter takes its bit source as an argument. Its semantic assumption is
that calls supply independent fair bits, which is not a property of arbitrary IO code.
-/

public section

open MeasureTheory PFunctor OracleComp

namespace ProbResponder

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- An executable fair-bit machine for each query, with its joint answer/state correctness law. -/
structure BitRealization (R : ProbResponder spec) where
  /-- A machine initialized with the service state and returning its answer and successor state. -/
  machine : (q : spec.Domain) → OracleMachine coinSpec R.State (spec.Range q × R.State)
  /-- The unbounded returned-output law equals the advertised joint kernel. -/
  returned_eq : ∀ q s,
    letI := R.instMeasurableSpaceRange q
    @Resumption.returnedMeasure coinSpec.toPFunctor (fun _ => ⊤) _ _ _ _
      ((machine q).denote s) = R.answerKernel q s

namespace BitRealization

variable {R : ProbResponder spec} (realization : BitRealization R)

/-- Execute through an injected bit source using the generic resumable IO driver. -/
def runIO (drawBit : IO Bool) (q : spec.Domain) (s : R.State) : IO (spec.Range q × R.State) :=
  (realization.machine q).runIO (fun _ => drawBit) ((realization.machine q).init s)

/-- Finite returned-output approximations are below the advertised service law. -/
theorem outputMeasure_le (q : spec.Domain) (s : R.State) (fuel : ℕ) :
    letI := R.instMeasurableSpaceRange q
    @Resumption.outputMeasure coinSpec.toPFunctor (fun _ => ⊤) _ _ _ fuel
      ((realization.machine q).denote s) ≤ R.answerKernel q s := by
  let := R.instMeasurableSpaceRange q
  rw [← realization.returned_eq]
  exact @Resumption.outputMeasure_le_returnedMeasure coinSpec.toPFunctor
    (fun _ => ⊤) _ _ _ _ fuel _

end BitRealization
end ProbResponder
