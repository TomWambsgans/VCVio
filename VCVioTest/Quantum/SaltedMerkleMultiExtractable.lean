/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Merkle.MultiExtractable

/-!
# Public salted Merkle aggregate contracts

An ordinary import exposes the concrete witnesses for every tuple code and varying bounded
depths, together with monotonicity of the scalar error bundle.
-/

public section

open Quantum SaltedMerkle Convexity
open scoped ENNReal

universe v w

example {X Y Msg Salt Z : Type} {k : ℕ} [Fintype X] [DecidableEq X]
    [Fintype Y] [LinearOrder Y] [AddCommGroup Y]
    [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
    [SampleableType Salt] [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (enc : Encoding X Y Msg Salt) (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg (fun i ↦ Td Y Salt (d i))) Z)
    (dmax : ℕ) (hd : ∀ i, d i ≤ dmax) :
    IsMultiExtractableWith.{v, w} (fun i ↦ (scheme enc (d i)).toVectorCommitment)
      (compressedVCOracle k X Y) (multiExtract enc d) code (fun _ ↦ tdBot)
      (StdSimplex.barycenter : StdSimplex ℝ (Fin k → X → Y))
      (fun H ↦ (romVCOracle k X Y H).mixedRuntime)
      (merkleErrors (Fintype.card Y) dmax) :=
  SaltedMerkle.isMultiExtractableWith enc d code dmax hd

example (N dmax : ℕ) : (merkleErrors N dmax).Monotone :=
  merkleErrors_monotone N dmax

/-- The total scalar definition also exposes its zero-query boundary. -/
example (N dmax : ℕ) (wVC wME : ℝ≥0∞) :
    (merkleErrors N dmax).offline 0 wVC wME 0 = 0 := by
  simp [merkleErrors, merkleOfflineError]
