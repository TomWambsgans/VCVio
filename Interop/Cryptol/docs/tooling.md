# Tooling integration and the semantic import boundary

The importer uses the official Cryptol frontend and specializer. The parser,
renamer, typechecker, module instantiation and typed-AST serialization remain an
explicit external assumption. A transformation after that boundary produces a
candidate, whose correspondence must be proved in Lean before an implementation
certificate is reused. Typechecking a candidate is insufficient.

The intended canonical target for broader imports is the pinned **normal
evaluator**. The current domain model and its partial-input theorems still
specify the reference evaluator. This tranche does not relabel those theorems:
normal/reference demand differences in the [audit](evaluators.md) are migration
obligations. The source importer, native representation theorem, external
execution check and security-game replacement theorem are separate claims.

## Implemented route

1. `cryptol-lean-export FOUNDATION MODULE ROOT...` loads and typechecks roots
   through the official Haskell library and exports their dependency closure.
2. `--specialize` additionally runs Cryptol's
   `Transform.Specialize.specializeEWhere`, returning **both** the original
   bundle and a candidate bundle. Primitive instantiations remain explicit.
3. `SourceElaboration.check bundle root` checks scope, kinds, closed constraints,
   the root schema and expression typing, then returns the canonical
   `Resolved.Term`, a scoped polynomial tree. The certificate retains the
   exact input and output equation, proved by Lean kernel reduction.
4. `ImportedSpecialization.accepted` checks the actual specializer output for
   Foundation's `sigma_256_0`. `ImportedSpecialization.correct` proves equality
   with the original import in the current partial model, including errors and
   bottom. `CertifiedFunction.congrSource` reuses its native implementation.
5. `ImportedSpecialization.core_correct` proves agreement with VCVio's actual
   `Sha2.ssig0` for every `UInt32`. The independent `Consumer` package uses
   ordinary imports. The existing contract and probability layers remain the
   interfaces for consumer proofs.

The specializer adapter needs a deliberate restriction. Cryptol 3.6.0's
[`specializeConst`](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/src/Cryptol/Transform/Specialize.hs)
clones `DPrim` declarations, freshens their names and removes the type arguments.
For `number`, these arguments contain the literal's value: the resulting
monomorphic `Integer` declaration does not identify that value. The adapter
excludes primitives from the specializable declaration cache, using the public
lower-level specializer API. It does not infer a missing value from a fresh name
or accept the transformation on trust. A regression changes rotation 7 to 8:
the mutated candidate still typechecks, but its kernel import certificate fails.

The typed importer also accepts monomorphic lexical `where` declarations,
finite sequence literals, tuples, records and projections, closed property
guards, and single-generator comprehensions of finite or infinite length. It
recognizes a bounded primitive fragment including integer addition,
multiplication and subtraction, literals, integer indexing and finite `foldl`.
Other instantiations fail explicitly. Nine official frontend canaries have
kernel-checked import equations; their semantic tests exercise captured locals,
higher-order functions, folds, and finite observations of infinite sequences.
The external driver compares original and lowered expressions in both evaluator
modes on 36 observations. These observations are regression evidence, not a
general preservation proof.

Source types remain attached to elaborated terms until the root schema has been
checked. Tuples lower to right-associated products ending in unit; record fields
use the frontend's canonical order. Source-type equality is kernel-reducible and
has a `LawfulBEq` proof. Its equality proof supplies typed transport. Thus two
records with different labels, or a record and a tuple with the same carrier,
cannot pass application/root checking merely because their Lean carriers match.

## Whole-Foundation discovery

`inventory_foundation.py` calls `--module` for every tracked `.cry` file at
Foundation `7d0528bd998682788f4e23661f2829298f9e47db`. All **135 files** load and
export through Cryptol 3.6.0. The committed census records 170 module/interface
records, including generated parameter interfaces; 15 are interfaces and 34
records have type or value parameters. It records 1,861 public value export
occurrences, of which 1,196 are marked properties by the official AST. These are
export occurrences across the loaded module records, not a count of independent
proved algorithms.

The census preserves schemas, module type/value parameters, constraints,
public type/nominal exports, nested functor/signature names, dependency paths,
source hashes, declaration line/column ranges and constructor counts. Declaration
locations use a basename within the containing module provenance; expression
locations remain a gap. Public-definition bodies include records, tuple
selection, comprehensions, local recursive groups, nominal cases and foreign
fallbacks. No regular-expression Cryptol parser was introduced.

Every module has separate, initially `not-attempted`, fields for Lean typing,
semantic import, native view, independent implementation equivalence and property
proofs. Individual certificates remain in the existing coverage catalogue. A
closed specialization certificate is not promoted to a polymorphic theorem for
its entire module. Ordinary validation checks the census format and pin;
external validation regenerates it through the official loader byte for byte.

## Architecture decisions

| Concern | Canonical choice in VCVio | Reason and remaining obligation |
|---|---|---|
| Official input | `Reference.Expr` and versioned `SourceBundle` | Mirror the external AST, retaining unresolved obligations for checking. This is input data, not a second typed computation model. |
| Checked monomorphic language | `Resolved.Term` on `ScopedSignature` / `IFreeM` | Intrinsic binding, type-preserving substitution and polynomial directions already exist. Labels are checking metadata, not a new evaluator. |
| Open quantifiers and module parameters | Existing `ScopedFamily` / `Polymorphic.Term` | Numeric/type/proof stages and simultaneous recursion require this extra information. General source elaboration into it remains missing. Do not approximate higher-order parameters with data-only codecs. |
| Partial meaning | Existing lifted domains and continuous functions | Error, divergence, suspended components and partial function arguments are relevant. Normal-evaluator migration must audit each affected demand rule. |
| Native data implementation | Existing `Finite.Term`, `Represents` and `CertifiedFunction` | This IR has executable total functions and preserves native word operations. The distinction earns its weight at the partial/total boundary; it is not another source language. |
| Contracts | Existing PolyFun correspondence plus VCVio's domain adapter | `congrSource` extends the existing certificate rather than adding a parallel transformation-contract hierarchy. |
| Execution | Existing `Control.Transition`, ITree and machine adapters | No heap evaluator was added just to obtain another model. A heap needs a measured sharing requirement and a simulation/adequacy obligation. |
| Core syntax | Existing `Expr` remains the operational/adequacy backend | It also has internal `force`; removing this carrier requires migrating those proofs and normal demand rules together. A second cosmetic polynomial wrapper would add a bridge without removing the duplicate. |

PolyFun already supplies the constant-family equivalence, renaming/substitution
laws, family reindexing, transition execution and ITree/machine bridges. The
companion's shared folds further reduce duplicate proof infrastructure. This
tranche does not need another generic carrier or contract predicate. PolyFun's
[model guide](https://github.com/Verified-zkEVM/PolyFun/blob/feat/cryptol-model/docs/guides/computation-models.md)
explains when free trees, resumptions, ITrees and dynamical machines retain
different useful information. They are useful viewpoints; importing Cryptol
does not require exposing all of them as competing VCVio APIs.

The open-PR audit on 2026-10-19 found three PolyFun drafts: [#290](https://github.com/Verified-zkEVM/PolyFun/pull/290)
at `103be8e` supplies the shared interop substrate; [#289](https://github.com/Verified-zkEVM/PolyFun/pull/289)
at `22752df` supplies independent example projects; [#308](https://github.com/Verified-zkEVM/PolyFun/pull/308)
at `d377c76` adds stateful service-machine composition. The current VCVio pin
already has every shared API needed by this tranche. None of these drafts needs
to be merged or imported wholesale to check the scalar specializer. Review the
generic #290 API before expanding the importer, use #289 to test independent
consumers, and bring #308 into scope when stateful service composition has an
actual Cryptol consumer. That keeps the dependency decision tied to a use case.

## Remaining investigation and implementation gates

The end-to-end specializer pilot is a **scalar**, not a replacement for the full
compression import. The existing SHA256 compression theorem still uses its
separate preserved-source extraction. The new typed-AST path does not yet cover
its full primitive closure, sequential/parallel comprehensions, local polymorphic
definitions and recursive groups. A source elaboration preservation theorem must
relate accepted constructors to the chosen normal semantics before this route
can establish general frontend correctness. A type certificate alone cannot do
that work.

The next compression gate is to elaborate the exact `Core::step` closure,
retaining dependency sharing, then replay the schedule/fold proof through that
certificate and recover the existing byte-function and adaptive-client theorems.
The next CRC gate is to elaborate `shared::CRC::Main` with its one type and seven
value parameters, connect imported `pmod` to the existing polynomial update
lemma, and prove incremental composition. The current CRC theorem is still about
transcribed equations. Module inventory success does not close either gate.

Normal semantics require more than changing integer division. The existing audit
finds packed-word comparison, shift/update demand, error precedence in function
arithmetic, folds and comprehension demand differences. Each migration needs a
semantic equation, regression on partial arguments and a review of affected
adequacy proofs. Infinite data must remain lazy where the normal implementation
is lazy; forcing all fields of every sequence is not a solution. Preserve the
original Foundation theta expression when changing semantics.

For broader language coverage, first use the census to select public modules and
instantiations, then implement one constructor/primitive family with typing,
semantics, native representation and consumer proofs. Keep property imports
separate from property proofs. Full hashes need padding and byte APIs in addition
to compression. AES and Keccak add useful word/array operations; ECDSA and the
algebra modules expose modular types, nominal cases and module interfaces.
These are concrete obligations toward “import all of Foundation”; this draft
does not claim that endpoint.

## Related tooling and ancestry

* Cryptol's official module loader, typed AST and specializer are the active
  dependency. Its `MonoValues` pass handles internal recursive polymorphic values
  for sharing; treating its output as another checked candidate is preferable to
  implementing that optimization independently. RPC is appropriate for a
  long-lived discovery/evaluation client; the linked Haskell adapter is needed
  for the typed graph and transformation entry points used here.
* [SAW's Cryptol integration](https://galoisinc.github.io/saw-script/master/saw-user-manual/proofs-about-cryptol.html)
  translates Cryptol into SAWCore and proves properties through its own tooling.
  SAW's [design paper](https://saw.galois.com/files/saw-vstte-final.pdf) motivates
  shared symbolic terms and normalization. SAW can be a future candidate producer;
  its ordinary solver result is not automatically a Lean proof artifact. Add a
  checked relation to SAWCore/exported terms before claiming that bridge.
* [Cryptol's Coq semantics](https://github.com/GaloisInc/cryptol-semantics) and
  `:extract-coq` are direct ancestry for importing Cryptol definitions into a
  prover. That project includes cryptographic examples connected to FCF; it is
  not evidence of complete current Cryptol semantics. The existing compression
  path here used the constructor dump; the linked typed-AST route avoids writing
  another source parser.
* [Allais, Atkey, Chapman, McBride and McKinna](https://arxiv.org/abs/2001.11001)
  provide the generic scoped-syntax/semantics ancestry. PolyFun's scoped and
  parameter-changing polynomial signatures make those concerns reusable rather
  than Cryptol-specific. The key question is whether specialization and proof
  transport use those shared laws, not whether another syntax datatype can be
  presented as a polynomial.
* The certificate approach follows translation validation: an external optimizer
  proposes a term and the prover checks the relationship required by the
  consumer. This is established architecture, not a novelty claim.
  [CryptHOL](https://isa-afp.org/entries/CryptHOL.html) and
  [EasyCrypt](https://github.com/EasyCrypt/easycrypt) are relevant ancestry for probabilistic program logic and game-based
  proofs; the measure-based VCVio replacement theorem is downstream of this
  deterministic importer. Neither their existence nor differential testing
  supplies Cryptol semantic preservation.
* [CV2EC](https://bblanche.gitlabpages.inria.fr/CryptoVerif/cv2EasyCrypt/) is a useful
  example of combining existing cryptographic proof tools through an explicit
  translation boundary. Its lesson for this project is architectural: use the
  upstream tool for the task it already performs, and identify the proof claim
  crossing the boundary. It is not a Cryptol importer or a Lean certificate checker.

The distinctive experimental combination is official Cryptol candidate generation,
scoped polynomial syntax, partial-domain reasoning, native Lean implementations
and direct VCVio game replacement. This tranche demonstrates the first three
with a checked scalar and reuses the established native bridge. A claim of novel
“full verified Cryptol interop” would be premature until the remaining language,
normal-semantics and whole-module gates are closed.
