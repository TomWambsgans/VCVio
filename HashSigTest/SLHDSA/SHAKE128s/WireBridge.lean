/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Wire

/-!
# Executable fixed-context wire query translation

The actual transformed adversary receives a recognizable encoded public key and signing
reply. A deterministic trace handler checks private sampling, repeated hash requests, signing
context and the final forgery without running FIPS key generation.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.WireBridgeTest

open Bridge

/-- Reject an observable mismatch with a nonzero executable exit. -/
def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"SHAKE-128s wire bridge check failed: {label}")

/-- A nonempty context whose framing is visible in both requests and the final forgery. -/
def context : SLHDSA.Security.PureContext := ⟨[0xCA, 0xFE], by decide⟩

/-- A typed public key with distinct seed and root bytes. -/
def publicKey : PublicKeyCore FIPS205.core :=
  ⟨Vector.replicate 16 0x12, Vector.replicate 16 0x34⟩

/-- Observable target queries, in chronological order. -/
inductive Event where
  | sample (index : Nat)
  | hash (input : Bytes)
  | sign (request : Message)
deriving DecidableEq

/-- The expected 30-byte hash reply. -/
def hashReply : FIPS205.Answer := Vector.replicate 30 0xA6

/-- The source program checks public-key encoding and every forwarded reply before forging. -/
def wireAdversary : StrongUnforgeableAdversary (wireAlgorithm context) where
  main key := do
    let sample : Fin 2 ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)) (.inl (.inl 1))
    let first : FIPS205.Answer ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes))
        (.inl (.inr [0x91]))
    let second : FIPS205.Answer ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes))
        (.inl (.inr [0x91]))
    let signature ← query (spec :=
      (unifSpec + SLHDSA.Security.shakeSpec FIPS205.params) + (Bytes →ₒ Bytes)) (.inr [0x41])
    return (if key == List.replicate 16 0x12 ++ List.replicate 16 0x34 &&
      sample.val == 1 && first == hashReply && second == hashReply then [0x42] else [], signature)

/-- Log actual target queries and answer with recognizable values. -/
def handler (answer : Option Bytes) :
    QueryImpl (Game.World FIPS205.Answer + Game.SigningSpec) (StateM (List Event))
  | .inl (.inl index) => do
      modify (· ++ [.sample index])
      return ⟨index, Nat.lt_succ_self index⟩
  | .inl (.inr input) => do
      modify (· ++ [.hash input])
      return hashReply
  | .inr request => do
      modify (· ++ [.sign request])
      return answer

/-- Execute the actual transformed adversary, without a challenger key-generation phase. -/
def run (answer : Option Bytes) : Game.Forgery × List Event :=
  (simulateQ (handler answer) ((fixedContextAdversary context wireAdversary).main publicKey)).run []

/-- The computable shared body is the program field of the actual transformation. -/
example : (fixedContextAdversary context wireAdversary).main publicKey =
    fixedContextMain context wireAdversary.main publicKey :=
  fixedContextAdversary_main context wireAdversary publicKey

/-- Check literal trace, byte and context observations, including the total fallback branch. -/
def check : IO Unit := do
  ensure "literal pure-mode frame" (context.encode [0x41] == [0, 2, 0xCA, 0xFE, 0x41])
  let expectedTrace : List Event := [
    .sample 1, .hash [0x91], .hash [0x91], .sign ⟨[0x41], [0xCA, 0xFE]⟩]
  let (forgery, trace) := run (some [0xBE, 0xEF])
  ensure "private, repeated-hash and context-attached signing queries" (trace == expectedTrace)
  ensure "encoded public key and forwarded oracle responses" (forgery.message.message == [0x42])
  ensure "final forgery context" (forgery.message.context == [0xCA, 0xFE])
  ensure "recognizable Some signing reply" (forgery.signature == [0xBE, 0xEF])
  let (fallback, fallbackTrace) := run none
  ensure "None reply still makes exactly one signing request" (fallbackTrace == expectedTrace)
  ensure "total None fallback" (fallback.signature == [])
  IO.println "SLH-DSA SHAKE-128s wire bridge: PASS (actual query translation; fixed context)"

end SLHDSA.SHAKE128s.WireBridgeTest

/-- Execute the fixed-context wire translation controls. -/
def main : IO Unit := SLHDSA.SHAKE128s.WireBridgeTest.check
