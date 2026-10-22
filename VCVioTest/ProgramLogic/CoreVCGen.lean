/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.NecessarySpecs

/-!
# Core `vcgen` on oracle computations

Core `vcgen` with the `@[spec]` rules of `VCVio.ProgramLogic.Unary.WP.NecessarySpecs`: uniform
draws, `$[0..n]`, replicated draws and lifts in the necessary reading.
-/

public section

namespace VCVioTest.ProgramLogic.CoreVCGen

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal

set_option experimental.vcgen true

section Necessary
open scoped OracleComp.Necessary

example : ⦃ True ⦄ (do let b ← $ᵗ Bool; let c ← $ᵗ Bool; pure (b || c || true) : ProbComp Bool)
    ⦃ fun r => r = true ⦄ := by
  vcgen
  simp

example (n : ℕ) : ⦃ True ⦄ ($[0..n]) ⦃ fun i => i.val ≤ n ⦄ := by
  vcgen
  omega

example : ⦃ True ⦄ ($ᵗ Bool).replicate 3 ⦃ fun xs => xs.length = 3 ⦄ := by
  vcgen
  grind

end Necessary

section liftComp

variable {τ : Type} {superSpec : OracleSpec τ} [unifSpec ⊂ₒ superSpec] [unifSpec ˡ⊂ₒ superSpec]

open scoped OracleComp.Necessary in
example : ⦃ True ⦄ liftComp ($[0..3]) superSpec ⦃ fun i => i.val ≤ 3 ⦄ := by
  vcgen
  omega

end liftComp

end VCVioTest.ProgramLogic.CoreVCGen
