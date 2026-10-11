/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Bridge.CompressionCertificate
import VCVio.Algorithms.Keccak

/-! # Public declarations named by the Foundation coverage catalogue -/

example := Interop.Cryptol.Bridge.compiledCompress_eq
example := Interop.Cryptol.Bridge.compression_byte_contract_iff
example := VCVio.Algorithms.Keccak.sha3Digest224
example := VCVio.Algorithms.Keccak.sha3Digest256
example := VCVio.Algorithms.Keccak.sha3Digest384
example := VCVio.Algorithms.Keccak.sha3Digest512
example := VCVio.Algorithms.Keccak.shake128
example := VCVio.Algorithms.Keccak.shake256
example := VCVio.Algorithms.Sha2.compress
example := VCVio.Algorithms.Sha2.sha224
example := VCVio.Algorithms.Sha2.sha256
example := VCVio.Algorithms.Sha2.sha384
example := VCVio.Algorithms.Sha2.sha512
example := VCVio.Algorithms.Sha2.sha512Trunc224
example := VCVio.Algorithms.Sha2.sha512Trunc256
