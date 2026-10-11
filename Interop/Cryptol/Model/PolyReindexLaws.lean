/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyReindex
import Mathlib.Tactic.CongrExclamation

/-!
# Coherence of symbolic constructor substitution

Identity and composition retain constructor data, including recursive groups
and constraint evidence. Checked result annotations compare by heterogeneous
equality so clients need not choose a distinguished equality witness.
These are head laws; whole-term traversal and semantic substitution laws require
compatibility with the lifted child maps as well.
-/

public section

namespace Interop.Cryptol.Polymorphic
namespace Op

/-- Equal word lengths give the same head, independent of constraint witnesses. -/
theorem wordLogic_heq {w : Scope} {l k : NumExpr w.numbers}
    (h : l = k) (op : BitOp) (hl : w.Entails (.fin l)) (hk : w.Entails (.fin k)) :
    HEq (Op.wordLogic l op hl) (Op.wordLogic k op hk) := by
  cases h
  rfl
/-- Identity parameter substitution preserves constructor data and its computed sort. -/
@[simp] theorem mapHead_id {w : Scope} {s : w.ValueSort} (op : Op w s) :
    op.mapHead (Scope.Map.id w) = ⟨s, op⟩ := by
  cases op <;> dsimp only [Op.mapHead, Scope.Map.id, Scope.Map.sort]
  case wordLogic l op h =>
    apply Sigma.ext
    · exact congrArg (fun k => Scheme.mono (.arrow (.seq k .bit)
        (.arrow (.seq k .bit) (.seq k .bit)))) (NumExpr.subst_id l)
    · exact wordLogic_heq (NumExpr.subst_id l) op _ _
  case letRec bs =>
    have hi : (Scope.Map.id w).sort = id := funext Scheme.subst_id
    change (⟨_, Op.letRec (bs.map (Scope.Map.id w).sort)
      ((Scope.Map.id w).sort s)⟩ : Sigma (Op w)) = _
    rw [hi, List.map_id]
    rfl
  all_goals congr! <;> try simp only [ParameterSubstitution.liftNum_id,
    ParameterSubstitution.liftType_id, ParameterSubstitution.apply_id,
    Scheme.subst_id]
  all_goals try simp only [ParameterSubstitution.id, NumExpr.subst_id, Constraint.subst_id]

/-- Successive substitutions of constructor data compose at all three binder kinds. -/
theorem mapHead_comp {w z u : Scope} (μ : Scope.Map w z) (ν : Scope.Map z u)
    {s : w.ValueSort} (op : Op w s) :
    (op.mapHead μ).2.mapHead ν = op.mapHead (μ.comp ν) := by
  apply Sigma.ext
  · simp only [Op.mapHead_result, Scope.Map.sort, Scheme.subst_subst]
    rfl
  · cases op <;> dsimp only [Op.mapHead, Scope.Map.comp, Scope.Map.sort]
    all_goals try exact wordLogic_heq (NumExpr.subst_subst _ _ _) _ _ _
    all_goals congr! 1 <;> try simp only [Scheme.subst_subst,
      ParameterSubstitution.apply_comp, ParameterSubstitution.liftNum_comp,
      ParameterSubstitution.liftType_comp]
    all_goals try simp only [ParameterSubstitution.comp, NumExpr.subst_subst,
      Constraint.subst_subst]
    all_goals try simp only [List.map_map, Scope.Map.sort,
      Scheme.subst_subst, Function.comp_def]
    all_goals try rfl

end Op
namespace Head

/-- A checked head is determined by its constructor data, across equal result sorts. -/
theorem heq_of_code_eq {w : Scope} {s t : w.ValueSort} {h : Head w s} {k : Head w t}
    (e : h.code = k.code) : HEq h k := by
  cases h with
  | mk hc he =>
    cases k with
    | mk kc ke =>
      cases e
      cases he
      cases ke
      rfl

/-- The identity retains a checked head, with no restriction on its result annotation. -/
@[simp] theorem map_id_heq {w : Scope} {s : w.ValueSort} (h : Head w s) :
    HEq (h.map (Scope.Map.id w)) h :=
  heq_of_code_eq (Op.mapHead_id h.code.2)

/-- Checked heads respect composition without exposing annotation transports. -/
theorem map_map_heq {w z u : Scope} (μ : Scope.Map w z) (ν : Scope.Map z u)
    {s : w.ValueSort} (h : Head w s) :
    HEq ((h.map μ).map ν) (h.map (μ.comp ν)) :=
  heq_of_code_eq (Op.mapHead_comp μ ν h.code.2)

end Head
end Interop.Cryptol.Polymorphic
