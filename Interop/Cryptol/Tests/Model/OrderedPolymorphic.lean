/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyRecursion
public import Interop.Cryptol.Model.PolyRenaming
public import Interop.Cryptol.Translation.PolymorphicExamples
public import PolyFun.IPFunctor.Scoped.FamilySize

/-! # Ordered stages, binding positions, finite descriptions and certificates -/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Tests.OrderedPolymorphic

open Polymorphic

/-- Two explicit instantiation stages. -/
@[expose] def stages : Scheme 0 0 := .allNum (.allType (.mono .bit))

private def early : Term Scope.empty [] stages := .error _ (.user "stage")

/-- Fail after the numeric stage. -/
@[expose] def middle : Term Scope.empty [] stages := .numAbs (.error _ (.user "stage"))

/-- Fail after both numeric and type stages. -/
@[expose] def late : Term Scope.empty [] stages := .numAbs (.typeAbs (.error _ (.user "stage")))

example : early.denote emptyAssignment (Env.empty _) = DomainResult.error (.user "stage") := rfl

example : middle.denote emptyAssignment (Env.empty _) =
    DomainResult.value (fun _ : Length =>
      (DomainResult.error (.user "stage") :
        DomainResult EvalError (ClosedTy → Computation .bit))) :=
  rfl

example : late.denote emptyAssignment (Env.empty _) =
    DomainResult.value (fun _ : Length => DomainResult.value
      (fun _ : ClosedTy => (DomainResult.error (.user "stage") : Computation .bit))) := rfl

/-- Each explicit quantifier preserves its own demand boundary. -/
theorem stages_distinct : middle.denote emptyAssignment (Env.empty _) ≠
    late.denote emptyAssignment (Env.empty _) := by
  intro h
  have he := congrFun (DomainResult.value_inj.mp h) (.finite 0)
  exact DomainResult.value_ne_error _ _ he.symm

private abbrev trivialConstraint : Constraint 0 := .eq (.finite 0) (.finite 0)

private def guarded : Term Scope.empty [] (.guard trivialConstraint (.allNum (.mono .bit))) :=
  Term.proofAbs (w := Scope.empty) trivialConstraint (.error _ (.user "guard"))

example : guarded.denote emptyAssignment (Env.empty _) ⟨rfl⟩ =
    DomainResult.error (.user "guard") := rfl

private abbrev twoTypes : Scope := ⟨0, 2, []⟩

private def mergeTypes : Scope.Map twoTypes Scope.empty :=
  ⟨⟨Fin.elim0, fun _ => .bit⟩, fun _ _ h => nomatch h⟩

private abbrev separate : List twoTypes.ValueSort := [.mono (.var 0), .mono (.var 1)]

private def first : Term twoTypes separate (.mono (.var 0)) := .var .zero

private def second : Term twoTypes separate (.mono (.var 1)) := .var (.succ .zero)

example : first.parameters mergeTypes =
    (Term.var .zero : Term Scope.empty [.mono .bit, .mono .bit] (.mono .bit)) := rfl

example : second.parameters mergeTypes =
    (Term.var (.succ .zero) : Term Scope.empty [.mono .bit, .mono .bit] (.mono .bit)) := rfl

example : first.parameters mergeTypes ≠ second.parameters mergeTypes := by
  intro h
  cases h

private def capture : Term Scope.empty [.mono .bit]
    (.allType (.mono (.arrow (.var 0) .bit))) :=
  .typeAbs (.lam (.var (.succ .zero)))

private def replaceBit : signature.Substitution (w := Scope.empty) [.mono .bit] []
  | _, .zero => Term.bit true
  | _, .succ x => nomatch x

example (a : ClosedTy) (x : Computation a) :
    DomainResult.applyContinuous ((capture.subst replaceBit).observe emptyAssignment
      (.type a (.mono (.arrow (.var 0) .bit) _)) (Env.empty _)) x =
        DomainResult.value ⟨true⟩ := rfl

private def localIdentity : Term Scope.empty []
    (.allType (.mono (.arrow (.var 0) (.var 0)))) := .typeAbs (.lam (.var .zero))

private def twoUses : Term Scope.empty [] (.mono (.prod .bit .integer)) :=
  .letE localIdentity
    (.pair (.app (.typeApp (.var .zero) .bit) (.bit true))
      (.app (.typeApp (.var .zero) .integer) (.integer 3)))

example : twoUses.denote emptyAssignment (Env.empty _) =
    DomainResult.value (DomainResult.value ⟨true⟩, DomainResult.value ⟨(3 : Int)⟩) := rfl

example : IPFunctor.ScopedFamily.Term.nodeCount Polymorphic.Examples.map = 11 := by decide

example : IPFunctor.ScopedFamily.Term.nodeCount Polymorphic.Examples.xor = 10 := by decide

example : IPFunctor.ScopedFamily.Term.nodeCount Polymorphic.Examples.shiftedCycle = 4 := by decide

example : Polymorphic.Examples.shiftedCycle.denote emptyAssignment (Env.empty _) ≠ ⊥ := by
  rw [Polymorphic.Examples.shiftedCycle_partial]
  exact DomainResult.value_ne_bot _

example (n : Nat) (x y : BitVec n) :
    DomainResult.applyContinuous
      (Finite.PolymorphicExamples.xorCertificate.meaningAt n).meaning
      (Finite.encodeData (.prod (.word n) (.word n)) (x, y)) =
        Finite.encodeData (.word n) (x ^^^ y) :=
  Finite.PolymorphicExamples.xorCertificate.correct n (x, y)

example : (Finite.PolymorphicExamples.xorCertificate.meaningAt 0).implementation
    ((0 : BitVec 0), (0 : BitVec 0)) = (0 : BitVec 0) := rfl

/-- Renaming an open recursive group retains one simultaneous fixed point. -/
example {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (bindings : List w.ValueSort)
    (rhs : (i : Fin bindings.length) → Term w (bindings ++ Γ) bindings[i])
    (body : Term w (bindings ++ Γ) s) (r : IPFunctor.ScopedSignature.Renaming Γ Δ)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote ((Term.letRec bindings rhs body).rename r) ρ η =
      (Term.letRec bindings rhs body).denote ρ (Env.rename ρ r η) :=
  Term.denote_rename _ r ρ η

/-- The general theorem also covers empty declaration groups. -/
example {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (body : Term w Γ s) (r : IPFunctor.ScopedSignature.Renaming Γ Δ)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote ((Term.letRec [] (fun i => Fin.elim0 i) body).rename r) ρ η =
      (Term.letRec [] (fun i => Fin.elim0 i) body).denote ρ (Env.rename ρ r η) :=
  Term.denote_rename _ r ρ η

end Interop.Cryptol.Tests.OrderedPolymorphic
