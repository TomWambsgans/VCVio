/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Model.Examples

/-! # Sequential and parallel generator demand and binding regressions -/

open Interop.Cryptol

example : (Resolved.lower (Resolved.Term.index Examples.dependentRows (.integer 1))).start.run
      2000 =
    .inl (.ok (.integer 10)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.dependentRows (.integer 2))).start.run
      2000 =
    .inl (.ok (.integer 2)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.parallelRows (.integer 1))).start.run
      1000 =
    .inl (.ok (.integer 12)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.parallelRows (.integer 2))).start.run
      1000 =
    .inl (.error (.invalidIndex 2)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.ignoredParallel (.integer 1))).start.run
      1000 =
    .inl (.ok (.integer 23)) := rfl

/-- An empty inner generator produces an outer value despite erroneous sources. -/
example : (Expr.force (Resolved.lower (Resolved.Term.flatMap (l := .infinite)
    (a := .integer) (b := .integer) 0 (.error (.user "function"))
      (.error (.user "sequence")))) (.integer 17)).start.run 100 =
    .inl (.ok (.integer 17)) := rfl
