/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.KernelHandler.Realizes
public import ToMathlib.MeasureTheory.MeasurableSpace.Except
public import ToMathlib.Control.Except
public import PolyFun.PFunctor.Free.Except

/-!
# Kernel correctness with explicit failure and retained state

Core `ExceptT` over `StateT` retains the service state on failure. Its finite
client law follows from `KernelHandler.Realizes.run` by exposing exceptional
answers through `PFunctor.withExcept`. The resulting measure includes errors
and their final state; no success conditioning or error-mass erasure is used.
-/

public section

open MeasureTheory ProbabilityTheory

namespace PFunctor.KernelHandler

universe uA u v

variable {P : PFunctor.{uA, u}} {S ε α : Type u} {m : Type u → Type v}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace ε]
  [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [Countable ε] [MeasurableSingletonClass ε] [MeasurableSpace α]

/-- Local joint error/answer/state laws determine the full law of an aborting finite client. -/
theorem Realizes.runExcept {K : KernelHandler (P.withExcept ε) S}
    {handler : Handler (ExceptT ε (StateT S m)) P}
    (h : K.Realizes handler.exceptAnswers) (program : FreeM P α) (state : S) :
    𝒟[((program.liftM handler).run).run state] =
      FreeM.runKernel K program.withExcept state := by
  have hrun := h.run program.withExcept state
  change 𝒟[((program.withExcept.liftM handler.exceptAnswers).run) state] = _ at hrun
  rw [FreeM.liftM_withExcept] at hrun
  exact hrun

end PFunctor.KernelHandler
