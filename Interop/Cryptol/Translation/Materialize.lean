/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.ModuleElaboration

/-!
# Materializing checked finite descriptions

Rendering consumes the checked polynomial tree, not the upstream AST. Generated
Lean constructor expressions are candidates: a separate kernel acceptance equation
checks them against elaboration of the original retained module. Keeping bodies
explicit avoids repeating frontend reduction inside downstream semantic proofs.
-/

public section

namespace Interop.Cryptol.Translation.Materialize

open Polymorphic

private def variableCode : Nat → String
  | 0 => ".zero"
  | n + 1 => s!"(.succ {variableCode n})"

private def app (name : String) (args : List String) : String :=
  "(" ++ name ++ " " ++ String.intercalate " " args ++ ")"

private def finiteCases : List String → String
  | [] => "(fun i => nomatch i)"
  | x :: xs => app "Fin.cases" [x, finiteCases xs]

private def op {w : Scope} : {s : w.ValueSort} → (head : Op w s) →
    (Fin head.arity → Except String String) → Except String String
  | _, .numAbs _, children => do
      return app "Term.numAbs" [← children 0]
  | _, .typeAbs _, children => do
      return app "Term.typeAbs" [← children 0]
  | _, .numApp _ e, children => do
      return app "Term.numApp" [← children 0, "(" ++ reprStr e ++ ")"]
  | _, .typeApp _ a, children => do
      return app "Term.typeApp" [← children 0, "(" ++ reprStr a ++ ")"]
  | _, .proofAbs c _, children => do
      return app "Term.proofAbs" ["(" ++ reprStr c ++ ")", ← children 0]
  | _, .proofApp _ _ _, children => do
      return app "Term.proofApp" [← children 0,
      "(by intro assignment; exact assignment.property _ (by simp))"]
  | _, .lam _ _, children => do
      return app "Term.lam" [← children 0]
  | _, .app _ _, children => do
      return app "Term.app" [← children 0, ← children 1]
  | _, .letE _ _, children => do
      return app "Term.letE" [← children 0, ← children 1]
  | _, .pair _ _, children => do
      return app "Term.pair" [← children 0, ← children 1]
  | _, .fst _ _, children => do
      return app "Term.fst" [← children 0]
  | _, .snd _ _, children => do
      return app "Term.snd" [← children 0]
  | _, .generate n _, children => do
      return app "Term.generate" ["(" ++ reprStr n ++ ")", ← children 0]
  | _, .index _ _, children => do
      return app "Term.index" [← children 0, ← children 1]
  | _, .ite _, children => do
      return app "Term.ite" [← children 0, ← children 1, ← children 2]
  | _, .fix _, children => do
      return app "Term.fix" [← children 0]
  | _, .letRec bs _, children => do
      let rhs ← (List.finRange bs.length).mapM (fun i => children i.succ)
      return app "Term.letRec" ["(" ++ reprStr bs ++ ")", finiteCases rhs, ← children 0]
  | _, .bit b, _ => do
      return app "Term.bit" [reprStr b]
  | _, .integer n, _ => do
      return app "Term.integer" ["(" ++ reprStr n ++ ")"]
  | _, _, _ => throw "constructor requires a public materialization rule"

/-- Render the accepted finite tree through its generic polynomial fold. -/
def term {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (body : Term w Γ s) : Except String String :=
  body.fold (P := signature.polynomial) (D := fun _ => Except String String)
    (fun _ x => .ok (app "Term.var" [variableCode x.index]))
    (fun _ head children => op head.code.2 children)

end Interop.Cryptol.Translation.Materialize
