# Cryptol model

The model is the `CryptolModel` library under `Interop/Cryptol` in VCVio's root
Lake project. It imports PolyFun, CSLib and Mathlib, with no dependency on VCVio
probability or cryptography. Its resolved source and native IR use PolyFun's
scoped polynomial carrier. The [project README](../README.md) owns build,
validation, CLI and local-dependency instructions.

## Specification boundary

The specification target is the reference evaluator distributed with Cryptol
3.6.0. Its [syntax and semantics references](../REFERENCES.md#cryptol360--cryptol-syntax-and-reference-semantics)
describe a tractable typed core, but do not remove the need to model laziness,
errors, and recursion. `Semantics.pdf` is generated from `Reference.lhs`;
the syntax PDF retains its historical Cryptol 2 title. The pinned reference
source is the authority when a PDF presentation is incomplete.

The Lean theorem relates **two Lean models of the fragment**. Neither the
Haskell evaluator nor Cryptol's parser/typechecker is verified by this work.
Resolved source has an independent
denotation and a proved lowering; the text printer is
validated with executable comparisons, not a parser/printer correctness proof.
Inbound clients supply a resolved, well-typed representation. There is no
parser, name resolver, type inference engine, or constraint solver.

| Axis | Checked model |
|---|---|
| Types | Bits, integers, unit, binary products, functions, finite and infinite sequences |
| Polymorphism | Separate numeric and value-type variables; prenex schemas; checked instantiation. A suspended-family domain and a changing-instantiation recursive spike are proved separately from resolved syntax. |
| Numeric expressions | Finite constants, infinity, variables, addition, multiplication, minimum; finiteness and equality constraints |
| Binding | Typed de Bruijn variables, capture-avoiding renaming/substitution, semantic substitution laws |
| Laziness | Suspended function arguments, let values, product fields, sequence elements; only the selected conditional branch is demanded |
| Recursion | Least fixed points at every closed type; monomorphic groups use lazy products. The polymorphic-domain extension takes one simultaneous fixed point over all valid instantiations. |
| Failure | Semantic bottom, explicit evaluation error, and returned outer value are distinct |
| Primitives | Structural zero; lazy finite folds; array arithmetic; Bit/integer operations; partial word logic, lexicographic comparison, modular arithmetic, conversions, dynamic shifts/rotations; structural sequence operations |
| Derived descriptions | Sequence literals, generators, map, parallel zip, finite-prefix append, observation windows; big-endian literals and finite total descriptions |

Products represent tuple spines. Named records, nominal types, local polymorphic
let bindings, arbitrary Cryptol type-class constraints, and the full numeric
type language are not included. Rational, modular-integer, float, foreign, and
cryptographic/security primitives are also outside the fragment. Word lowerings compile to the core, using `Expr.force` to demand an outer
constructor without demanding its components. `force` is internal: `Resolved.Term`
retains named source primitives, and `Export.coreExpression?` rejects a bare core
term containing `force`. Neither `trace` nor `deepseq` is substituted for it.

The reference demand rules are explicit:

- Word logic demands its input outer constructors, then suspends output bits.
- Arithmetic and integer conversion demand complete words; conversion from
  an integer demands that integer even at width zero.
- Comparisons demand both outer constructors and then compare from the most
  significant bit, stopping at the first difference.
- Dynamic shifts demand the amount first. Word amounts go through unsigned
  `toInteger`; negative integer shifts retain invalid-index behavior. Rotations
  use Euclidean normalization. Empty rotations preserve their source after
  demanding the amount.
- A finite left fold builds nested suspended applications. An empty fold ignores
  its function and source; a constant step may ignore both accumulator and element.
  Structural zero constructs aggregates and constant functions. Array arithmetic
  demands both outer arrays even at length zero.
- Structural operations generate lazy output constructors. `take front back`
  requires an input of length `front + back`; `drop` has a finite front;
  `join`/`split` have finite row width; transpose accepts infinite dimensions.
  Empty dimensions satisfy `0 * inf = inf * 0 = 0`.
- Indexing demands the outer sequence before the index. Update demands the
  index first and can return a replacement without demanding the source.
  The reference's negative update index is accepted and changes no element.

`Expr.observePrefix` is a separate observation window; it may exceed a finite
source and encounter an index error. It is not the source `take` primitive.

## What is proved

[`Domain.lean`](../Model/Domain.lean) gives each value type an omega-CPO.
Computations are `WithBot (DiscreteOrder EvalError ⊕ Value)`. Products and
sequences contain **computations**, and functions are continuous maps between
computation domains. Thus a returned pair or stream can still have an
undefined component. [`Denotation.lean`](../Model/Denotation.lean)
defines a continuous map from environments by structural recursion on syntax;
the recursive binding case takes a least fixed point. Its definition does
not refer to machine fuel.

[`Operational.lean`](../Model/Operational.lean) is a total,
call-by-name transition system with typed frames and suspended closed terms.
The fuel runner returns an outcome or an exact residual. `MachineState.run_add`
proves that splitting the budget preserves that result. This evaluator does
not memoize suspended lets, so its step counts are not Cryptol runtime costs.
Its soundness and adequacy include the internal `force` frame.

[`Adequacy.lean`](../Model/Adequacy.lean) proves:

- `Expr.related_denote`: the fundamental logical relation under related
  semantic environments and syntactic substitutions. Admissibility handles
  recursive approximation at sequences, products, and higher-order types.
- `Expr.adequacy_value`: an outer semantic value exists exactly when execution
  terminates with a runtime value having that denotation.
- `Expr.adequacy_error`: a semantic error exists exactly when execution returns
  that error.
- `Expr.adequacy_bottom`: bottom is exactly absence of a terminating outcome.
- `Definition.adequacy`: the relation holds at every valid schema instantiation.

[`Observation.lean`](../Model/Observation.lean) extends this interface
to finite projection, indexing, and application paths. Its `denote_apply` law
connects the observation syntax and meaning. This is how to state a correctness
claim about a finite demand on a stream or function without asserting that the
whole value is total. [`Words.lean`](../Model/Words.lean) proves
`Expr.denote_word` for every width and proves the bitvector representation injective.

[`Laws.lean`](../Model/Laws.lean) exposes public denotation equations
and a function-extensionality rule. [`WordOps.lean`](../Model/WordOps.lean)
and [`WordArithmetic.lean`](../Model/WordArithmetic.lean) prove BitVec
laws, including modular arithmetic and conversions. A hypothesis
`e.denote ρ = .value (wordValue x)` asserts that every bit is defined; an outer
sequence constructor alone is insufficient.

[`WordSemantics.lean`](../Model/WordSemantics.lean),
[`WordCompare.lean`](../Model/WordCompare.lean),
[`WordShift.lean`](../Model/WordShift.lean), and
[`SequenceOps.lean`](../Model/SequenceOps.lean) give direct partial
semantics and lowering equations on arbitrary suspended inputs.
`Semantics.shiftFixed_eq_shift` identifies fixed nonnegative movements with
the dynamic reference operation, including partial sources.
[`SequenceLaws.lean`](../Model/SequenceLaws.lean) exposes selected-element
laws. An elementwise round trip does not imply equality of outer computations:
`join (split (error ...))` exposes a constructor before demanding the source.

## Finite descriptions and specification transfer

[`Finite.lean`](../Translation/Finite.lean) gives a smaller typed language
an independent interpretation in `Bool`, `BitVec`, products, finite arrays,
and Lean functions. It supports lambda abstraction, application, lexical lets,
word logic, fixed shifts/rotations, and modular addition/subtraction/multiplication. `Term.lower_correct` relates this interpretation to the lazy core
for all terms, including higher-order terms, under related environments.
At word types the relation requires the entire output word to be defined.
At function types it requires preservation of related arguments. It makes no
claim about applying total native functions to partially defined core inputs.

[`FiniteSource.lean`](../Translation/FiniteSource.lean) preserves named
primitive heads and lets. `Term.source_correct` relates its independent source
meaning to the native interpreter; `source_lower_correct` composes this with
`Resolved.lower_correct`. Source text therefore stays compact when the core
lowering is large.

[`Quote.lean`](../Translation/Quote.lean) supplies a small Lean quotation
language with lexical names and shadowing:

```lean
open Interop.Cryptol Interop.Cryptol.Finite

def shared : Finite.Term [] (.arrow (.word 32) (.word 32)) :=
  [cryptol| fun x => let y := rotr x 7; let x := y + 1; x ^ y]
```

The expected type supplies widths. Unknown names fail during elaboration.
This quotation creates a checked description; it does not parse Cryptol files.

[`Representation.lean`](../Translation/Representation.lean) provides
`DataShape`, canonical `encodeData`, uniqueness of represented data, and
`Term.denote_apply_data`. Products encode multiple arguments and finite arrays
encode multiword state. [`Contracts.lean`](../Translation/Contracts.lean)
then transports arbitrary preconditions and postconditions after an all-input
native equality `∀ x, f.denote Env.empty x = g x`:

```text
DataContract inputShape f.lower pre post  ↔  ∀ x, pre x → post x (g x)
```

Use `Term.dataContract_iff` for direct lowering or
`Term.source_dataContract_iff` for `Resolved.lower f.source`. The word-specific
`Term.totalContract_iff` remains available.

The left side includes a fully represented result, rather than just a
conditional assertion about terminating executions. Adequacy then supplies
termination of every in-range bit observation. `Term.property_iff` connects
finite Boolean predicates to core truth assertions. Exporting a property to
Cryptol additionally requires a finite description of the predicate; arbitrary
Lean propositions and proofs are not printable Cryptol programs.

[`Certified.lean`](../Translation/Certified.lean) retains a resolved source and a
finite implementation with a complete-output equality on represented inputs.
`CertifiedFunction.contract_iff` transfers arbitrary predicates without exposing
the recurrence proof. `Recurrence.lean` supplies the constructor-producing,
strict-prefix fixed-point rule; `Finite/Loop.lean` constructs shared finite
prefix tables and iterations. `ResolvedSequences.lean` supplies ranges and
single-generator comprehensions, with partial denotation equations.

A downstream Foundation/VCVio consumer reifies a monomorphic source AST while
retaining its fixed point and fold. Lean then checks the recurrence compilation
and its correspondence to a VCVio byte-array function. The frontend, erased
constraints, and structural AST reifier remain trusted; the text printer is tested.
Even a reproducible typed-AST artifact is not a proof of the Haskell frontend.
Cryptographic function names, distributions, stateful oracle replacement,
Foundation fixtures, and security claims belong in that downstream consumer.

## PolyFun connections

[`Resolved.lean`](../Model/Resolved.lean) presents source syntax as a shared
`ScopedSignature.Term`: an `IPFunctor.IFreeM` with typed variables at its leaves.
Directions select typed children, including beneath binders.
[`NativePrimitives.lean`](../Model/NativePrimitives.lean)
provides instantiated primitive constants with independent denotations.
`Primitive.lower_correct` and `Resolved.lower_correct` relate source meaning
to core meaning for arbitrary partial environments. Generic folds implement both
syntax translations and interpretation; their fusion and substitution laws also
support independent language developments.

For source proofs, use the equations in `ResolvedLaws` together with
`Environment.extend_zero` and `Environment.extend_succ`. These preserve named
environments during normalization. Unfolding the entire environment function
under continuous maps can make kernel conversion much more expensive than the
corresponding constructor proof.

`MachineState.tree` exposes each transition as a guarded ITree silent step.
[`MachineDomain.lean`](../Model/MachineDomain.lean) proves
`Expr.denote_eq_treeDenote`: interpreting that tree through the generic PolyFun
continuous-algebra API equals the independently defined language semantics.
The exact `ITree.machine` adapter makes the same tree available to resumable
execution over `P + y`.

The generic additions are reusable outside the model:

- `ToCslib/Order/`: continuous currying, least fixed points, admissibility,
  and omega-CPOs for discrete types, disjoint sums, bottom lifting, and finite
  strict-prefix recurrences. `ToCslib/Data/Fin/Cases.lean` adds proved compiler
  simplifications for finite case/vector lookup at the pinned Lean version.
- `PolyFun/Control/Domain/Result.lean`: errors and partial information with
  continuous strict sequencing.
- `PFunctor.Resumption.denote`: continuous-algebra semantics; agreement with
  well-founded `FreeM` folds; lens transport; supremum of finite truncation folds.
- `ITree.denote`: silent steps interpreted by identity; exact agreement with
  the resumption representation and corecursive state equations; invariance
  under weak bisimulation.

[`FiniteWP.lean`](../Tests/Model/FiniteWP.lean) exercises the local v4.35
`ExactWPMonad` API for the total budgeted runner. Its postcondition explicitly
handles residuals. A policy accepting a cutoff is not a termination proof.
The model installs no global WP instance. Continuous-algebra semantics does
not add a `LawfulMonadIter` instance for the family of typed semantic domains;
the existing generic ITree monadic interpreters remain a separate interface.

## External evidence and evaluator discrepancies

The corpus has 26 fixtures: lazy errors and divergence, productive and mutual
recursion, an instantiated polymorphic map, factorial and higher-order calls,
empty and out-of-bounds sequences, signed integer arithmetic, and word examples.
Twenty-five terminating fixtures are compared against **both** external
evaluators. Kernel-checked regression examples also establish semantic claims
from concrete machine executions.

The word matrix checks 1,160 total cases at widths 0, 1, 2, 3, 8, 32, and 64.
Small widths exhaust all pairs for bitwise and modular arithmetic; larger widths
include boundary patterns and negative/oversized rotations. Independent integer
calculations, machine observations, compact exports and native Cryptol operators
are compared. Kernel tests additionally cover erroneous amounts, partial words,
short-circuit comparisons, structural operations, empty dimensions and update
selection. Cutoff stays distinct from both errors and semantic divergence.

[`Inspect.lean`](../Model/Inspect.lean) supplies constructor counts and
a counted runner proved equal to `run`. Core observations use fresh budgets and
repeat work. The `arx-native` command instead executes a total finite description
and exports its retained lets. At depths 1, 2, 4 and 8, both 32- and 64-bit probes
have 13, 25, 49 and 97 source nodes (340, 657, 1,291 and 2,559 source bytes).
Native values and both external evaluators agree. These measurements diagnose
usability; they are not a resource or Cryptol runtime theorem.

Cryptol 3.6.0's evaluators disagree on negative integer division:

| Expression | Lean model and Cryptol reference | Cryptol normal |
|---|---:|---:|
| `(-7 : Integer) / 3` | -2 | -3 |
| `(-7 : Integer) % 3` | -1 | 2 |

The reference uses Haskell `quot`/`rem`; the Lean core uses `Int.tdiv`/`Int.tmod`.
The external driver checks the normal evaluator's distinct results explicitly.
It does not silently count those two comparisons as semantic agreement.
This is a reason to retain the versioned reference boundary in any broader model.

The driver also pins demand differences, rather than silently treating normal
and reference evaluation as equivalent:

| Expression | Reference/model | Normal evaluator |
|---|---|---|
| `([True] # (error "tail" : [7])) @ 0` | `True` | tail error |
| `([False, error "late"] : [2]) == [True, False]` | `False` | late error |
| `update ([False, True] : [2]) (-1 : Integer) True` | unchanged input | invalid index |
| `((error "source" : [4]) << (4 : Integer)) @ 0` | `False` | source error |
| `(update (error "source" : [2]) (0 : Integer) True) @ 0` | `True` | source error |

The reference's empty `foldl` ignores an erroneous function and sequence. A
constant step can also ignore an erroneous accumulator and nonempty sequence.
Normal evaluation forces the sequence's outer constructor in both cases and
returns its error. The driver records both differences explicitly, alongside
structural zero, lazy map, integer comparison error order, and empty-array
arithmetic demand checks.

The concatenation difference persists when rotating to its defined bit.
Partial comprehensions remain lazy in both evaluators. The target is the pinned
reference semantics; total BitVec theorems do not establish normal-evaluator
agreement on arbitrary partial words.

## Extending the pilot

Keep the operational core small. Add a source primitive with a continuous direct
meaning and a lowering proof before extending core syntax. Use public equations,
canonical data representations and named quotation in clients. Test outer errors,
partial fields, negative indices, zero sizes and finite/infinite dimensions.

The downstream Foundation pilot certifies full SHA-256 compression: an arbitrary
8-word state and 16-word block, the recursive 64-word schedule, all 64 rounds,
and feed-forward. A byte-boundary theorem covers an eight-word `Array UInt32`
and any valid 64-byte window, with explicit big-endian decoding and no alignment
restriction. Arbitrary byte contracts and adaptive response/state replacement
follow there. Full hashing, padding, and a general recursion compiler remain
outside this milestone.

The finite native interpreter retains computed scalar lets and is the intended
executable path for large total descriptions. The adequate core machine remains
call-by-name; it is useful for bounded demand probes and does not claim practical
full-compression performance. Source normalization uses named scalar equations
to avoid expensive repeated unfolding of dependent semantic carriers.

The [upstream ledger](upstream.md)
records the relevant local v4.35 base, fork PRs, and public CSLib PRs. It also
identifies which definitions should replace local owners at a coordinated pin
upgrade. Probability and security interpretations belong downstream in VCVio.

## Coverage and gap ledger

| Capability | Current evidence | Remaining boundary |
|---|---|---|
| Shared syntax | Resolved and native terms are `ScopedSignature.Term`; generic rename/substitution laws, fold fusion, relational folds and reindexing | The shared binding signature handles value binders; type binders that change the ambient context still need language-specific representation and laws |
| Native semantics | One constructor algebra and generic semantic substitution; source preservation composes with resolved lowering | Native fragment is total and monomorphic |
| Recurrence compilation | Prefix uniqueness, least-fixed-point agreement, compact singleton extension and a linear syntax-size theorem | No general termination compiler or evaluation-time certificate |
| Polymorphic recursion | Suspended schema families; simultaneous recursive-group fixed point; strict continuous fixed-point fusion; changing-instantiation regression | No resolved `ETAbs`/`ETApp`/local-polymorphic-group syntax-to-domain theorem yet |
| Language semantics | Closed typed core, operational soundness and adequacy, lazy words/sequences, explicit errors | Records, nominal/enumeration types, rational and modular integers, full numeric functions/constraints, full comprehensions, trace/deepseq/random are absent |
| Opaque operations | Unsupported operations are rejected by the importer | Floating point, arrays and foreign backends need explicit semantic interfaces and conditional correspondence proofs |
| Inbound transport | Preserved pinned SHA-256 typed dump, scoped structural reifier, rejection tests and generated-artifact checks | `:extract-coq` erases information; a general typed-AST exporter and Lean decoder remain to be built |
| Outbound transport | Typed resolved printer and comparisons with both pinned evaluators | No formal parser/printer round trip or Haskell correctness proof |
| Foundation | SHA-256 compression for all finite state/block values and valid byte windows; adaptive VCVio replacement | CRC, whole-hash padding and cryptographic security claims remain outside the certificate |

The semantic-domain spike deliberately retains an outer result around each
polymorphic family. Taking only a product of monomorphic computations would
identify distinct demand behaviors. The generic sort-reindexing API preserves
binding positions under a noninjective instantiation, but it is not a substitute
for these quantified-value semantics.
