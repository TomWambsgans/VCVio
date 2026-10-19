# Foundation compatibility implementation

This checkpoint implements the artifact and linking part of the broader plan.
It does **not** complete all-Foundation semantic import. All 135 pinned files
pass decoding, scope/kind checking and interface validation; all 155 owned
module instances link structurally. The corpus now attempts typed elaboration
of every instance and records actual failures. The production obligation ledger
remains empty: no implementation or preservation theorem has been admitted.

## The implemented boundary

The frontend is Cryptol `61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`, optionally
with the reviewed `case-binder-types.patch`. The pinned Foundation revision is
`7d0528bd998682788f4e23661f2829298f9e47db`. The patch rewrites case-bound field
annotations during backtick module instantiation. Its canonical Git diff SHA-256 is
`cffd4082d3347aba60c131d2e7d33f8b8fdfaf6afa4aedd52d8d2fff7bb30a2e`.
Artifacts record the base revision and ordered patch digests separately. The
driver checks the exact tracked source diff, not merely a dirty-tree flag.
The original malformed matrix annotation is retained as a negative fixture.

Module bundle version 3 retains interfaces as complete parameter telescopes,
constraints and synonym bodies. Lean validates them, even when they are only
dependencies of the requested module. Unsupported nested functor/signature
definitions fail explicitly; none occurs in the pinned corpus. This does not
claim support for arbitrary future Cryptol modules.

`Reference.Expr.freeValues` handles every retained expression constructor,
including sequential and parallel comprehension bindings, case fields, lexical
groups and simultaneous recursion. `SourceScope` checks the computed dependencies
against metadata. Metadata cannot remove a real dependency from the linker.
Fuel exhaustion is an error. Duplicate global IDs, inconsistent name spellings,
unknown nominal types, unresolved interface synonyms and incomplete declaration
metadata are rejected.

`SourceLink` retains whole recursive groups, includes official fallback targets,
and schedules groups by their body dependencies. A cycle between separate
nonrecursive groups is rejected. A `PrimitiveRequirement` has evidence that its
source form is primitive or foreign without a body. All four foreign definitions
in this Foundation revision have bodies and remain ordinary implementations.
The `ModuleBundle.LinkCertificate` records exact checker acceptance.

`ModuleElaboration` consumes that link result and puts primitive meanings in the
existing typed environment before module value parameters. There is no second
oracle language or monad for these requirements. Primitive schemes are checked
by the same open type checker as ordinary declarations. An unsupported scheme
or body remains a rejection. Module selection uses a retained module name;
the result carries the exact module found in the bundle.

Seeded `random`, when reached, is a deterministic primitive requirement with a
seed argument. This does not supply a probability interpretation, claim a
uniform distribution, or identify the reference and normal evaluators. The
same principle applies to backend-specific demand/trace behavior.

## Current semantic coverage

The 155 typed attempts produce four entries without value definitions, two
parameterized scalar operator modules, the complete Imperative module, and the
complete common/properties module conditional on three primitives. The latter
requires `==`, `!=` and `True` with their complete schemes. These are explicit
semantic inputs, not evidence that those primitives implement Cryptol equality.
Imported property declarations are functions returning bits, not proved facts.

The 147 rejected instances have these first blockers:

| Boundary | Instances |
|---|---:|
| Partial numeric type/application interpretation | 115 |
| Constraint entailment | 12 |
| Aggregate/nominal source types | 8 |
| Field constraints | 6 |
| Prime constraints | 3 |
| Expression constructors | 2 |
| Scheme equality | 1 |

The report intentionally does not infer per-declaration failure from a module's
first error. Declaration stages change only when whole-module elaboration
actually succeeds. Empty modules are not counted as executable successes.
Selected bundles retain all bodies for independent local regression checking;
the full corpus is reproducible through the official loader.

## Remaining implementation, in dependency order

1. **Canonical partial numeric types.** Migrate `PolyTy`, parameter substitution,
   assignment interpretation, `Scheme.domain`, and numeric/type application
   together from `NumExpr` to `NumericExpr`. Type interpretation must require
   successful evaluation under valid assignments. Preserve ordered quantifiers
   and proof guards: a guard can justify a later partial size. Do not choose
   zero/infinity for an undefined expression or add another permanent open
   language beside `ScopedFamily`. Reprove the existing transport/substitution
   laws and migrate public bridges in the same change.
2. **Proof-producing entailment and casts.** Recognize numeric/type constraints
   using Lean proofs. Unsolved constraints become explicit proof obligations;
   upstream SMT success is not a Lean certificate. Include definedness in numeric
   equality, and check source shape before erasing record or tuple labels.
3. **Value coverage and primitive implementations.** Add source-shaped tuples,
   records and lazy nominal sums, then rational and modular values with explicit
   errors. Implement the required primitive family against the documented lazy
   semantics, keeping backend compatibility separate. Finish cases, updates,
   guards and sequential/parallel comprehensions. Floating-point support is not
   required by this pinned Foundation corpus; do not conflate that fact with
   complete future-language support.
4. **Ordered module semantics.** The linker now checks and preserves group
   boundaries, but the typed module's meaning still uses the existing global
   `Env.fixGroup`. Replace that semantic flattening with ordered `letE`/`letRec`
   composition, or prove the precisely stated equivalence for checked schedules.
   Merely retaining group metadata is not that theorem. Complete interface
   instantiation and checked cross-bundle renaming as real consumers require them.
5. **Source preservation and native consumers.** State independently what the
   exported source AST means. Make elaboration produce a derivation relating
   that AST to the canonical term; prove the derivation sound. Complete the
   List/Sort/Enum native views, imported CRC update/chunk correspondence, and
   full SHA256 padding/message-processing equality. Reuse `CorrespondsOn`,
   `CertifiedMeaning` and the adaptive handler replacement theorems.

These are still unfinished work in the original implementation plan. A named
theorem admission may be useful for a precisely stated preservation obligation;
an admitted body or a fabricated native value must not count as import coverage.

## Haskell and proof ancestry

The adapter continues to link the official parser, renamer, typechecker, module
loader and candidate specializer. Constructor wire tags are now explicit,
exhaustive matches rather than an accidental dependency on Haskell `Show`.
Python checks provenance, orchestrates jobs and quotes constructors. Lean owns
dependency recomputation, scopes, kinds, linking and typed elaboration.

The strong proof starting point is the **exact exported AST**. Its relationship
to source bytes still depends on the identified frontend and serializer. The
driver's source hashes and differential tests do not verify Haskell. A future
upstream export API could reduce custom adapter code further; porting Cryptol's
whole frontend or verifying all of Haskell is not a prerequisite here.

Use existing polynomial folds and semantic certificates to compose these claims:

```text
artifact acceptance
  + source-elaboration preservation
  + any candidate-transformation preservation
  + total native representation correspondence on valid inputs
  → direct implementation replacement in a VCVio client
```

Each premise has a separate status. Acceptance alone cannot imply the later
arrows. The [literature survey](evaluators.md) and [tooling report](tooling.md)
trace the ancestry through Cryptol's reference/Coq semantics and FCF, SAW's
extraction and primitives-as-parameters, translation validation, generic binding
syntax, and game-based frameworks such as CryptHOL and EasyCrypt. This tranche's
contribution is the concrete checked compatibility/linking boundary and its
whole-corpus application in Lean; it is not a claim of the first verified
Cryptol importer or of full language interoperability.
