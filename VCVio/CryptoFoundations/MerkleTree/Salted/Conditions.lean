/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.HalfPreimage
public import VCVio.Quantum.VC.Conditions

/-!
# Salted Merkle conditions

The salted Merkle multi-extractor satisfies the algebraic `Quantum.Conditions` with the empty
trapdoor and collision-free good databases. Admissibility uses the distinct-index convention of
`Quantum.MultiExtractor.Admissible`; extractor efficiency remains a separate obligation.
-/

public section

open Quantum OracleComp

namespace SaltedMerkle

variable {X Y Msg Salt : Type} [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt] [SampleableType Salt]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : Fin k → ℕ)

/-- Salted Merkle commitments satisfy the classical sufficient conditions for multi-extraction. -/
theorem conditions :
    Conditions (fun i ↦ (scheme enc (d i)).toVectorCommitment)
      (fun i ↦ checkIOForm enc (d i)) (multiExtract enc d) (fun _ ↦ tdBot) collisionFree where
  admissible := multiExtract_admissible enc d
  empty_mem := empty_mem_collisionFree
  binding hk idx hidx cm ans pf Ds hD h i := by
    obtain ⟨ha, hp⟩ := multiExtract_binding enc d hk idx hidx cm ans pf Ds hD h i
    refine ⟨ha, ?_⟩
    intro pf' hpf'
    have heq : pf' = opening (d i) (ans i).dom
        ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).2 := by
      simpa [scheme, DetVectorCommitment.toVectorCommitment] using hpf'
    exact heq.trans hp
  valid hk idx hidx cm Ds i pf hpf := by
    have heq : pf = opening (d i)
        ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).1.dom
        ((multiExtract enc d).extract (TpIC.full hk idx cm) Ds i).2 := by
      simpa [scheme, DetVectorCommitment.toVectorCommitment] using hpf
    subst pf
    exact multiExtract_valid enc d hk idx hidx cm Ds i

end SaltedMerkle
