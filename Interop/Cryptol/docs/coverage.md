# Foundation coverage and conformance

[`coverage.json`](../coverage.json) records the public entry points selected for
reference coverage, their parameter and input profiles, semantic requirements,
known dependencies, native counterparts and current proof strength. It is an
inventory of the intended corpus, not a claim that every entry is modeled.

`planned` means no Lean source correspondence is available. `probe` records
external evaluation or a small transcribed statement. `certified` requires a
Lean theorem relating the retained source to the named implementation for every
input in the stated profile. Executable test vectors never promote an entry to
`certified`. Source provenance and evaluator agreement remain separate from
kernel checking. Dependency lists marked `partial` are investigation leads;
only the compression dependency closure is currently extracted and pinned.

The bridge validation checks the catalogue schema, source pins, declaration
references and status invariants. Its external pass loads the listed public
modules and asks the pinned Cryptol frontend for each entry's type. A successful
load is not a supported importer, a semantic preservation theorem, or a proof of
the source property. The existing compression source, recurrence compilation,
byte boundary and adaptive-client theorems remain the first complete chain.

## Endpoint and order

The first corpus endpoint is reference coverage of the non-ECDSA algorithm
families plus CRC, followed by a P-256 pilot. Full correspondence with actual
core implementations is first required for all SHA2 and SHA3/SHAKE variants.
Other families may initially have imported references and source properties
without an independently verified native implementation. New source features
must first pass partial-value and binder regressions, rather than being erased
by the importer to make a particular algorithm compile.

1. Close whole-term parameter/value substitution laws. Constructor-head
   identity/composition and numeric/type lifting coherence are proved; the
   generic PolyFun map/substitution law is conditional on local reindexing
   naturality. Discharge that condition for Cryptol and prove semantic
   substitution while preserving ordered quantifier stages and simultaneous
   recursion. Keep source and implementation separate.
2. Introduce a pinned typed-AST exporter and a checked Lean decoder. Retain
   constraints, declaration groups, nominal declarations, guards,
   comprehensions, module provenance and foreign declarations' pure fallbacks.
   Reproduce the existing compression certificate through both inbound paths.
3. Add partial numeric type operations and class constraints; heterogeneous
   aggregates with lazy selection/update; full comprehensions; nominal cases;
   then modular/rational and remaining reference primitives. Extend operational
   adequacy to polymorphic stages. Floating point and backend arrays follow the
   deterministic corpus; unsupported reference primitives retain their errors.
4. Certify reusable bounded folds, prefix recurrences and finite stream
   observations, then full SHA256 padding/block processing, SHA2 variants,
   CRC/AES and Keccak/SHA3/SHAKE. Expand compositions and the remaining families
   before tackling P-256 arithmetic and termination.

## What a guard establishes

A semantic certificate establishes equality in Lean of the imported meaning and
an actual implementation on an explicit admissible domain. This permits pulling
or pushing any Lean pre/postcondition over that domain. For a represented Boolean
source property, truth requires a defined `true` result: divergence and error
cannot satisfy the property. Bits and bytes require a proved codec and a stated
alignment restriction; an all-bit-length source claim does not follow from a
byte-oriented implementation theorem.

Checks of the source pin, dependency closure, typed export and printer protect
the trusted connection to Cryptol. Kernel checking protects the Lean semantic
proof and implementation correspondence. Differential evaluation protects
against mismatches at those trusted boundaries. None subsumes the others. A
Cryptol/SAW solver result is independent evidence unless its certificate is
checked in Lean.

The next property-transfer cases are Keccak's state-conversion inverses and a
CRC update/concatenation law with the appropriate alignment and parameter
hypotheses. Mutation tests should alter constants, byte order, shifts, field
selection, constraint evidence and instantiations, and report which gate rejects
each mutation. Record proof and execution costs alongside semantic coverage.
