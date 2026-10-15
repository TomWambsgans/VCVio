/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Salted.HalfPreimage

/-!
# Tests for salted Merkle trees

Toy instances of the salted Merkle commitment of ePrint 2025/2166, Def 8.2, with one-bit labels,
messages and salts and tagged oracle inputs:

* depths `d = 0` and `d = 1`, with their `CheckIO` forms and perfect completeness;
* an honest commitment for an explicit hash function, opened and checked by evaluation;
* `MTExtract` evaluated on a small explicit database, its validity, and Lemma 8.6 on it.
-/

public section

namespace VCVioTest.SaltedMerkleCanary

open SaltedMerkle Quantum

/-- Tagged inputs: node inputs on the left, leaf inputs `(m, γ)` on the right. -/
abbrev X := (Bool × Bool) ⊕ (Bool × Bool)

/-- The tagged encoding. -/
def enc : Encoding X Bool Bool Bool where
  node := Sum.inl
  leaf := Sum.inr
  node_injective := Sum.inl_injective
  leaf_injective := Sum.inr_injective

/-! ## Depths `0` and `1` -/

example : VectorCommitment X Bool Bool Bool (Td Bool Bool 0) (Pf Bool Bool 0) 1 := scheme enc 0

example : VectorCommitment X Bool Bool Bool (Td Bool Bool 1) (Pf Bool Bool 1) 2 := scheme enc 1

example : (scheme (Msg := Bool) enc 0).PerfectlyComplete := perfectlyComplete enc 0

example : (scheme (Msg := Bool) enc 1).PerfectlyComplete := perfectlyComplete enc 1

/-- At depth `1`, an opening of both positions makes at most `2 · 2 = 4` checks. -/
example : (checkIOForm (Msg := Bool) enc 1).qVC 2 = 4 := rfl

/-- At depth `0`, the one opening lists at most `2 · 1 - 1 = 1` distinct pair. -/
example (rt : Bool) (ans : PartialVec 1 Bool) (td : Td Bool Bool 0) (io : List (X × Bool))
    (h : outputIO enc 0 rt ans (opening 0 ans.dom td) = some io) : io.length ≤ 1 :=
  length_outputIO_opening_le enc rt ans _ td io h

/-! ## An honest commitment, opened and checked -/

/-- A hash function that tells nodes and leaves apart and is not symmetric in its arguments. -/
def H : X → Bool
  | .inl (a, b) => a && !b
  | .inr (m, γ) => m != γ

/-- The committed message `(true, false)`. -/
def msg : Fin 2 → Bool := ![true, false]

/-- The salts `(false, false)`. -/
def salts : Fin 2 → Bool := ![false, false]

/-- The leaf labels are `H (true, false) = true` and `H (false, false) = false`, and the root is
`H (true, false) = true`. -/
example : (honestTree enc 1 H msg salts).1 = true := by decide

/-- Opening both positions lists three distinct pairs: the two leaf pairs, and the root pair,
which both paths share, once. -/
example : (outputIO enc 1 (honestTree enc 1 H msg salts).1 (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2)).map List.length = some 3 := by
  decide

/-- The honest opening of both positions passes the check. -/
example : (checkIOForm enc 1).checkOn (fun x ↦ some (H x)) (honestTree enc 1 H msg salts).1
    (PartialVec.restrict msg Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) = true := by decide

/-- A wrong answer is rejected. -/
example : (checkIOForm enc 1).checkOn (fun x ↦ some (H x)) (honestTree enc 1 H msg salts).1
    (PartialVec.restrict ![false, false] Finset.univ)
    (opening 1 Finset.univ (honestTree enc 1 H msg salts).2) = false := by decide

/-! ## Extraction from an explicit database -/

/-- The database of the honest tree above: the two leaf queries and the root query. -/
def D : Database X Bool
  | .inr (true, false) => some true
  | .inr (false, false) => some false
  | .inl (true, false) => some true
  | _ => none

/-- `MTExtract(true, D)` recovers the message and the salts. -/
example : (extract enc 1 true D).1 = ![some true, some false] := by decide

example : (extract enc 1 true D).2.1 = ![some false, some false] := by decide

/-- The extracted labels: the root, then the leaf labels. -/
example : labelAt (extract enc 1 true D).2.2 1 0 = some true ∧
    labelAt (extract enc 1 true D).2.2 1 1 = some false := by decide

/-- From the root `false`, which has no preimage in `D`, nothing is extracted. -/
example : (extract enc 1 false D).1 = fun _ ↦ none := by decide

/-- The extracted message passes the check on its domain (Thm 8.4 condition 3). -/
example : (checkIOForm enc 1).checkOn D true (extract enc 1 true D).1
    (opening 1 (extract enc 1 true D).1.dom (extract enc 1 true D).2) = true :=
  extract_valid enc 1 true D

/-- Lemma 8.6 on the empty database, whose half-preimages are empty: an entry with output
`false ≠ rt` does not change the extraction from `true`. -/
example : extract enc 1 true (Function.update Database.empty (.inl (true, true)) (some false)) =
    extract enc 1 true Database.empty :=
  extract_eq_of_not_mem enc rfl (by simp [halfPreimages, Database.empty])

/-- An entry whose output is the root can change the extraction: after adding
`(false, true) ↦ true`, the root `true` has the lexicographically first preimage `(false, true)`,
and the leaves swap. -/
example : (extract enc 1 true (Function.update D (.inl (false, true)) (some true))).1 =
    ![some false, some true] := by decide

end VCVioTest.SaltedMerkleCanary
