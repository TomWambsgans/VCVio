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
The partial-table checks require every prescribed cell to contain its value. These conditions
feed the checked-read extraction theorem without changing the scheme or its opening algorithm.

## References

Chiesa, Di, Hu and Zheng, ePrint 2025/2166: admissibility (Definition 7.1, p. 49),
the Merkle scheme (Definition 8.2, pp. 52–53), and the sufficient conditions
(Theorem 8.4, pp. 53–54). The Merkle instantiation uses `MTMultiExtract` (p. 55)
and the collision-free conditions in the proof of Theorem 8.3 (pp. 55–56).
-/

public section

open Quantum OracleComp

namespace SaltedMerkle

/-- Finite labels and salts give finitely many typed trapdoors. -/
instance instFiniteTd {Y Salt : Type*} [Finite Y] [Finite Salt] (d : ℕ) :
    Finite (Td Y Salt d) := by
  have htree (n : ℕ) : Finite (BinaryTree.FullData (Option Y) (BinaryTree.Skeleton.perfect n)) := by
    induction n with
    | zero =>
        exact Finite.of_surjective BinaryTree.FullData.leaf
          (by intro t; cases t; exact ⟨_, rfl⟩)
    | succ n ih =>
        let := ih
        exact Finite.of_surjective
          (fun p : Option Y × BinaryTree.FullData (Option Y) (BinaryTree.Skeleton.perfect n) ×
              BinaryTree.FullData (Option Y) (BinaryTree.Skeleton.perfect n) =>
            BinaryTree.FullData.internal p.1 p.2.1 p.2.2)
          (by
            intro t
            cases t with
            | internal value left right => exact ⟨(value, left, right), rfl⟩)
  let := htree d
  exact inferInstanceAs (Finite ((Fin (2 ^ d) → Option Salt) ×
    BinaryTree.FullData (Option Y) (BinaryTree.Skeleton.perfect d)))

/-- Optional salts and typed perfect trees form a finite trapdoor register. -/
noncomputable instance instFintypeTd {Y Salt : Type*} [Fintype Y] [Fintype Salt] (d : ℕ) :
    Fintype (Td Y Salt d) := Fintype.ofFinite _

variable {X Y Msg Salt : Type} [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt] [SampleableType Salt]
  (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) {k : ℕ} (d : Fin k → ℕ)

/-- Salted Merkle commitments satisfy the classical sufficient conditions for multi-extraction. -/
theorem conditions :
    Conditions (fun i ↦ (scheme enc (d i)).toVectorCommitment)
      (fun i ↦ nonadaptiveCheck enc (d i)) (multiExtract enc d) (fun _ ↦ tdBot) collisionFree where
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
