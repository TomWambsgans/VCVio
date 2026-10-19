/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.SourceScope
public import Interop.Cryptol.Translation.OpenElaboration
public import Interop.Cryptol.Model.PolyDenotation

/-!
# Shared typed module environments

Each retained declaration has one finite polymorphic body. Global references
are positions in a typed environment; linking ties one simultaneous least
fixed point before specialization. Module value parameters remain explicit
ambient inputs. Acceptance witnesses certify the elaboration result only;
frontend correctness and source-semantic preservation are separate claims.
-/

public section

namespace Interop.Cryptol.Translation

open Polymorphic

/-- A module and its shared, intrinsically typed declaration bodies. -/
structure ElaboratedModule where
  /-- Exact retained source module, including its provenance and exports. -/
  source : ModuleDefinition
  /-- Module numeric/type parameters and their assumptions. -/
  scope : Scope
  /-- Explicit value parameters, in source order. -/
  parameters : List (Reference.Name × scope.ValueSort)
  /-- Every declaration in the selected transitive closure, once. -/
  declarations : List (Reference.Name × scope.ValueSort)
  /-- Bodies refer to the shared declaration context and ambient value parameters. -/
  bodies : (i : Fin (declarations.map Prod.snd).length) →
    Term scope (declarations.map Prod.snd ++ parameters.map Prod.snd)
      (declarations.map Prod.snd)[i]

namespace ElaboratedModule

/-- Link all declarations before choosing any instantiation of their schemes. -/
@[expose] noncomputable def denote (m : ElaboratedModule) (ρ : m.scope.Assignment) :
    Env ρ (m.parameters.map Prod.snd) →𝒄 Env ρ (m.declarations.map Prod.snd) :=
  IPFunctor.ScopedDomain.Env.fixGroup (fun s => s.domain ρ.val)
    (fun i => (m.bodies i).denote ρ)

/-- The shared declaration environment satisfies all defining equations simultaneously. -/
theorem denote_unfold (m : ElaboratedModule) (ρ : m.scope.Assignment)
    (η : Env ρ (m.parameters.map Prod.snd)) :
    m.denote ρ η = IPFunctor.ScopedDomain.Env.ofFin (fun s => s.domain ρ.val)
      (fun i => (m.bodies i).denote ρ (Env.append ρ (m.denote ρ η, η))) :=
  IPFunctor.ScopedDomain.Env.fixGroup_unfold _ _ _

/-- Select a public source name and retain the shared declarations around its reference. -/
@[expose] def exportTerm (m : ElaboratedModule) (name : String) :
    Except String (OpenElaboration.TypedTerm m.scope (m.parameters.map Prod.snd)) := do
  let exported := m.source.exports.filter (fun n => n.text == name)
  let [identity] := exported | throw "unknown or ambiguous public declaration"
  let globals := OpenElaboration.Names.extendMany
    (OpenElaboration.Names.ofSignatures (w := m.scope) m.parameters) m.declarations
  let ⟨s, body⟩ ← OpenElaboration.lookup globals identity
  return ⟨s, .letRec (m.declarations.map Prod.snd) m.bodies body⟩

end ElaboratedModule

namespace ModuleBundle

/-- Include all own definitions and their transitive value dependencies and official fallbacks. -/
@[expose] def declarationClosure (bundle : ModuleBundle) (root : ModuleDefinition) :
    List Reference.Decl := Id.run do
  let all := bundle.modules.flatMap fun m => m.groups.flatMap Reference.DeclGroup.declarations
  let metadata := bundle.modules.flatMap ModuleDefinition.declarations
  let mut needed := (root.groups.flatMap Reference.DeclGroup.declarations).map Reference.Decl.name
  for _ in List.range (all.length + 1) do
    let previous := needed
    for info in metadata do
      if previous.contains info.name then
        needed := needed ++ info.dependencies.filter (fun n => !needed.contains n)
    for (original, fallback) in bundle.primitiveFallbacks do
      if needed.contains original && !needed.contains fallback then needed := needed ++ [fallback]
    if needed == previous then break
  return all.filter fun d => needed.contains d.name

/-- Module binders retain their source identities while extending the canonical parameter scope. -/
@[expose] def parameters : (w : Scope) → OpenTypes.Parameters w.numbers w.types →
    List (Reference.Name × Reference.Parameter) →
    Except String ((z : Scope) × OpenTypes.Parameters z.numbers z.types)
  | w, env, [] => .ok ⟨w, env⟩
  | w, env, (_, p) :: rest => match p.kind with
      | .number => parameters w.bindNum (env.bindNum p.id) rest
      | .value => parameters w.bindType (env.bindType p.id) rest
      | _ => .error "unsupported module parameter kind"

/-- Elaborate a complete module into one typed shared environment. -/
@[expose] def elaborate (bundle : ModuleBundle) (root : ModuleDefinition)
    (fuel : Nat := 10000) : Except ImportError ElaboratedModule := do
  let checked := bundle.checkModuleScopes root fuel
  match checked with
  | .error e => throw e
  | .ok () => pure PUnit.unit
  let result : Except String ElaboratedModule := do
    let ⟨⟨w, env⟩⟩ ← OpenElaboration.liftCheck
      (parameters Scope.empty ⟨[], []⟩ root.typeParameters)
    let ⟨cs⟩ ← OpenElaboration.liftCheck (root.constraints.mapM (OpenTypes.constraint env fuel))
    let scope : Scope := ⟨w.numbers, w.types, cs ++ w.constraints⟩
    let ⟨ambient⟩ ← OpenElaboration.liftCheck
      (root.valueParameters.mapM fun (name, schema) => do
        return (name, ← OpenTypes.scheme env fuel schema))
    let selected := bundle.declarationClosure root
    let ⟨sigs⟩ ← OpenElaboration.liftCheck
      (OpenElaboration.signatures (w := scope) env fuel selected)
    let names := OpenElaboration.Names.extendMany
      (OpenElaboration.Names.ofSignatures (w := scope) ambient) sigs
    let resolved := selected.map fun d =>
      match bundle.primitiveFallbacks.find? (fun entry => entry.1 == d.name) with
      | some (_, target) => Reference.Decl.mk d.name d.schema (.expression (.var target))
      | none => d
    let rhs ← OpenElaboration.bodies fuel (w := scope) env names resolved sigs
    return ⟨root, scope, ambient, sigs, rhs⟩
  result.mapError (⟨[root.provenance.name, "elaboration"], ·⟩)

/-- An exact accepted module elaboration, independent of source-preservation claims. -/
structure ElaborationCertificate (bundle : ModuleBundle) (source : ModuleDefinition) where
  /-- Explicit checking budget. -/
  budget : Nat
  /-- Typed module with real bodies. -/
  result : ElaboratedModule
  /-- Kernel-checked acceptance equation. -/
  accepted : bundle.elaborate source budget = .ok result

/-- Successful elaboration retains its exact acceptance equation. -/
@[expose] def certifyElaboration (bundle : ModuleBundle) (source : ModuleDefinition)
    (fuel : Nat := 10000) : Except ImportError (bundle.ElaborationCertificate source) :=
  match h : bundle.elaborate source fuel with
  | .ok result => .ok ⟨fuel, result, h⟩
  | .error error => .error error

end ModuleBundle
end Interop.Cryptol.Translation
