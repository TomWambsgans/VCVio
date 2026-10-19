/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ImperativeBodies
import all Interop.Cryptol.Translation.SourceScope
import all Interop.Cryptol.Translation.OpenTypes
import all Interop.Cryptol.Translation.OpenElaboration
import all Interop.Cryptol.Translation.ModuleElaboration
import all Interop.Cryptol.Model.Reference.Kinds
import all Interop.Cryptol.Model.Reference.Types
import all Interop.Cryptol.Model.Reference.Syntax
import all Interop.Cryptol.Model.Types
import all Interop.Cryptol.Model.Scheme
import all Interop.Cryptol.Model.Length
import all Interop.Cryptol.Model.Parameters
import all Interop.Cryptol.Model.PolyScope

/-!
# Imported Foundation imperative utilities

Both definitions come from the retained whole module through the open importer.
Their natural interface accepts lazy continuous functions and suspended states.
General loops may diverge; their semantics does not claim a total Lean function.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Bridge.Imperative

open Polymorphic Translation

set_option maxRecDepth 10000

/-- Kernel reduction checks the candidate against the complete retained source. -/
theorem import_accepted :
    ImperativeSource.bundle.elaborate ImperativeSource.source 1000 = .ok imported := by
  with_unfolding_all
    change Except.ok _ = Except.ok imported
    congr 3
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i

/-- The complete source import, carrying its exact kernel-checked acceptance equation. -/
@[expose] def certificate :
    ImperativeSource.bundle.ElaborationCertificate ImperativeSource.source :=
  ⟨1000, imported, import_accepted⟩

/-- The finite while export retains the whole shared declaration group. -/
@[expose] def whileSource : Term Scope.empty [] loopScheme :=
  Term.letRec (w := Scope.empty) (Γ := []) [loopScheme, loopScheme] imported.bodies (.var .zero)

/-- The finite do-while export retains the same shared declaration group. -/
@[expose] def dowhileSource : Term Scope.empty [] loopScheme :=
  Term.letRec (w := Scope.empty) (Γ := []) [loopScheme, loopScheme] imported.bodies
    (.var (.succ .zero))

/-- The selected while is exactly the public export of the checked module. -/
theorem export_while : imported.exportTerm "while" = .ok ⟨loopScheme, whileSource⟩ := by
  with_unfolding_all rfl

/-- The selected do-while is exactly the other public export of the checked module. -/
theorem export_dowhile : imported.exportTerm "dowhile" = .ok ⟨loopScheme, dowhileSource⟩ := by
  with_unfolding_all rfl

/-- Checked specialization of the loop's sole type parameter. -/
@[expose] def loopInstance (a : ClosedTy) : Specialization loopScheme emptyAssignment.val
    (.arrow (.arrow a .bit) (.arrow (.arrow a a) (.arrow a a))) :=
  .type a (.mono _ _)

/-- Apply the imported while to lazy functions and a possibly partial initial state. -/
@[expose] noncomputable def whileLoop {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a) : Computation a :=
  DomainResult.applyContinuous
    (DomainResult.applyContinuous
      (DomainResult.applyContinuous
        ((loopInstance a).run (imported.denote emptyAssignment (Env.empty _)
          loopScheme .zero)) condition) body)
    initial

/-- Apply the imported do-while without imposing totality on its callbacks or state. -/
@[expose] noncomputable def doWhileLoop {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a) : Computation a :=
  DomainResult.applyContinuous
    (DomainResult.applyContinuous
      (DomainResult.applyContinuous
        ((loopInstance a).run (imported.denote emptyAssignment (Env.empty _)
          loopScheme (.succ .zero))) condition) body)
    initial

/-- Applying the exported source term gives the public loop interface. -/
theorem whileSource_apply {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a) :
    DomainResult.applyContinuous
      (DomainResult.applyContinuous
        (DomainResult.applyContinuous
          (whileSource.observe emptyAssignment (loopInstance a) (Env.empty _)) condition) body)
      initial = whileLoop condition body initial := by
  simp only [Term.observe, ContinuousHom.comp_apply, whileSource,
    Term.denote_letRec, Term.denote_var]
  rfl

/-- Applying the exported do-while term gives the same shared-environment interface. -/
theorem dowhileSource_apply {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a) :
    DomainResult.applyContinuous
      (DomainResult.applyContinuous
        (DomainResult.applyContinuous
          (dowhileSource.observe emptyAssignment (loopInstance a) (Env.empty _)) condition) body)
      initial = doWhileLoop condition body initial := by
  simp only [Term.observe, ContinuousHom.comp_apply, dowhileSource,
    Term.denote_letRec, Term.denote_var]
  rfl


set_option maxHeartbeats 800000 in
-- Reducing the shared polymorphic body checks the dependent environments and type transports.
/-- Unfold the imported loop once, retaining the lazy callback and state demands. -/
theorem whileLoop_unfold {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a) :
    whileLoop condition body initial = Semantics.conditional
      (whileLoop condition body (DomainResult.applyContinuous body initial), initial)
      (DomainResult.applyContinuous condition initial) := by
  with_unfolding_all
    let run : Env emptyAssignment [loopScheme, loopScheme] → Computation a := fun η =>
      DomainResult.applyContinuous (DomainResult.applyContinuous
        (DomainResult.applyContinuous ((loopInstance a).run (η loopScheme .zero)) condition)
        body) initial
    exact congrArg run (imported.denote_unfold emptyAssignment (Env.empty _))

set_option maxHeartbeats 800000 in
-- Reducing the shared polymorphic body checks the dependent environments and type transports.
/-- Do-while tests the state after the first body application. -/
theorem doWhileLoop_unfold {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a) :
    doWhileLoop condition body initial = Semantics.conditional
      (whileLoop condition body (DomainResult.applyContinuous body initial),
        DomainResult.applyContinuous body initial)
      (DomainResult.applyContinuous condition (DomainResult.applyContinuous body initial)) := by
  with_unfolding_all
    let run : Env emptyAssignment [loopScheme, loopScheme] → Computation a := fun η =>
      DomainResult.applyContinuous (DomainResult.applyContinuous
        (DomainResult.applyContinuous ((loopInstance a).run (η loopScheme (.succ .zero))) condition)
        body) initial
    exact congrArg run (imported.denote_unfold emptyAssignment (Env.empty _))


/-- A false condition returns the suspended state without demanding the body. -/
theorem whileLoop_eq_of_false {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a)
    (h : DomainResult.applyContinuous condition initial = .value ⟨false⟩) :
    whileLoop condition body initial = initial := by
  rw [whileLoop_unfold, h]
  rfl

/-- A true condition takes one body step before checking the condition again. -/
theorem whileLoop_eq_step_of_true {a : ClosedTy}
    (condition : Computation (.arrow a .bit)) (body : Computation (.arrow a a))
    (initial : Computation a)
    (h : DomainResult.applyContinuous condition initial = .value ⟨true⟩) :
    whileLoop condition body initial =
      whileLoop condition body (DomainResult.applyContinuous body initial) := by
  rw [whileLoop_unfold, h]
  rfl

/-- A false constant condition returns the suspended initial state. -/
theorem whileLoop_false {a : ClosedTy} (body : Computation (.arrow a a))
    (initial : Computation a) :
    whileLoop (.value (.const (.value ⟨false⟩))) body initial = initial := by
  rw [whileLoop_unfold]
  rfl

/-- With a false condition, do-while returns exactly one lazy body application. -/
theorem doWhileLoop_false {a : ClosedTy} (body : Computation (.arrow a a))
    (initial : Computation a) :
    doWhileLoop (.value (.const (.value ⟨false⟩))) body initial =
      DomainResult.applyContinuous body initial := by
  rw [doWhileLoop_unfold]
  rfl

/-- Failure to obtain the condition is observable even when the body is unused. -/
theorem whileLoop_error {a : ClosedTy} (error : EvalError)
    (body : Computation (.arrow a a)) (initial : Computation a) :
    whileLoop (.error error) body initial = .error error := by
  rw [whileLoop_unfold]
  rfl

end Interop.Cryptol.Bridge.Imperative
