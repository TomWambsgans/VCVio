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
| Polymorphism | Ordered numeric, type, and proof binders; checked instantiation and local polymorphic values; one finite syntax tree before instantiation |
| Numeric expressions | Finite constants, infinity, variables, addition, multiplication, minimum; finiteness and equality constraints |
| Binding | Typed de Bruijn positions and capture-avoiding transformations; semantic substitution laws for the monomorphic core/native IR; beta laws for ordered polymorphic syntax |
| Laziness | Suspended function arguments, let values, product fields, sequence elements; only the selected conditional branch is demanded |
| Recursion | Least fixed points at every closed type; monomorphic groups use lazy products. Finite polymorphic group syntax takes one fixed point of the whole scheme environment before instantiation. |
| Failure | Semantic bottom, explicit evaluation error, and returned outer value are distinct |
| Primitives | Structural zero; lazy finite folds; array arithmetic; Bit/integer operations; partial word logic, lexicographic comparison, modular arithmetic, conversions, dynamic shifts/rotations; structural sequence operations |
| Derived descriptions | Sequence literals, generators, map, parallel zip, finite-prefix append, observation windows; big-endian literals and finite total descriptions |

Products represent tuple spines. Named records, nominal types,
arbitrary Cryptol type-class constraints, and the full numeric
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

## Ordered polymorphic syntax and semantics

[`Scheme.lean`](../Model/Scheme.lean) retains the order of numeric, type, and
proof binders. Every numeric or type quantifier introduces a fresh outer
`DomainResult` around its family. Thus an error before any instantiation, an
error after a numeric argument, and an error after a subsequent type argument
are distinct meanings. Proof binders range over checked evidence and add no
suspension. `Scheme.domain_subst` identifies the complete pointed domains under
parameter substitution, including their order and bottom.

[`PolyScope.lean`](../Model/PolyScope.lean) tracks free parameters and numeric
assumptions. A `Scope.Map` supplies numeric and type expressions and proves
that they preserve assumptions. [`PolyReindex.lean`](../Model/PolyReindex.lean)
implements one constructor-local `ScopedFamily.Hom`; the generic PolyFun
traversal performs the tree recursion. Instantiating two distinct type
parameters to the same type preserves the two value-variable positions.
[`PolySubstitution.lean`](../Model/PolySubstitution.lean) uses that action to
move value substitutions under parameter binders without capturing variables.
Its identity and renaming-interaction laws follow from the shared PolyFun API.
[`PolyRenaming.lean`](../Model/PolyRenaming.lean) proves `Term.denote_rename` for
every current constructor, including numeric/type/proof abstractions, single
recursion and simultaneous recursive groups. The proof uses positional
environment transport and whole-group fixed-point naturality. A general
semantic theorem for parameter and value substitution is not yet provided.

[`PolySyntax.lean`](../Model/PolySyntax.lean) stores finite heads and finitely
many children. Heads carry checked result annotations separately from their
constructor data, so type transport does not obscure recursive positions.
[`PolyConstructors.lean`](../Model/PolyConstructors.lean) hides identity context
casts for ordinary clients. The syntax includes numeric/type/proof abstraction
and application, local polymorphic lets, heterogeneous recursive groups,
functions, products, generators, indexing, and selected primitives. A closed
resolved term embeds through `Term.closed`.

[`PolyDenotation.lean`](../Model/PolyDenotation.lean) folds the tree into
continuous environment maps at each valid parameter assignment. Recursive
groups use the generic `ScopedDomain.Env.fixGroup`: recursive calls can select
different instantiations because the fixed point is taken before specialization.
[`PolyLaws.lean`](../Model/PolyLaws.lean) exposes numeric/type/value beta laws,
erased proof application, lazy lets, and exact agreement of the closed embedding
with `Resolved.denote`. These are denotational laws. The monomorphic abstract
machine and adequacy theorem do not yet cover this syntax.
`Specialization` selects a meaning; it does not produce a resolved AST. The
existing source printer also remains monomorphic.

[`PolyExamples.lean`](../Model/PolyExamples.lean) gives a single 11-node map
description at all finite and infinite lengths, with selected-element meaning
on arbitrary suspended functions and sources. Its XOR description has 10 nodes
independent of width. [`PolyRecursion.lean`](../Model/PolyRecursion.lean) proves
that a recursive call at `n + 1` can yield a returned family whose every instance
is bottom; a two-binding group produces the constant true family through a call
at a changed instantiation. Neither example unfolds a family of host-generated
syntax trees. The older flat `Schema` domain API in `Polymorphic.lean` remains
available; the ordered API is the syntax-facing development.

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

[`SemanticCertificate.lean`](../Translation/SemanticCertificate.lean) factors
the representation contract over a semantic computation, independent of which
syntax denotes it. [`CertifiedFamily.lean`](../Translation/CertifiedFamily.lean)
retains one finite polymorphic source together with implementations and
all-input representation proofs for every instance of an explicit
`FamilyInterface`. Its `contract_iff` pulls or pushes arbitrary preconditions
and postconditions at those instances. The interface determines the scope of
the theorem; it need not cover every possible specialization of the source.
[`PolymorphicExamples.lean`](../Translation/PolymorphicExamples.lean) certifies
XOR for **every** natural width and every pair of words, including width zero.
This transfer uses a denotational equality and does not require a new evaluator.

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
  continuous strict sequencing and elimination into arbitrary pointed domains.
- `PolyFun/IPFunctor/Scoped/Family*.lean`: context-changing finite syntax,
  constructor-local parameter maps, value substitutions, and finite node counts.
  The generic traversal composition and relational fold laws also support the
  independent polymorphic tutorial in PolyFun.
- `PolyFun/Control/Domain/Pointed.lean` and `IPFunctor/Scoped/Domain.lean`:
  bundled domains, continuous heterogeneous environments, and one simultaneous
  least fixed point for a finite binding group.
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
Constant maps over a finite erroneous source remain lazy in both evaluators.
For an infinite erroneous source, the reference returns the constant at a
selected index while normal evaluation reports the source error. The ordered
polymorphism matrix checks 34 observations covering map demand, empty lengths,
local polymorphism, numeric instantiation, and XOR at seven widths. These are
handwritten Cryptol counterparts, not an extraction theorem for the new syntax.
An empty integer sequence displays as `0` in the reference and `[]` in normal
evaluation; the driver treats this as a presentation difference.
The target is the pinned
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
| Shared syntax | Resolved/native terms use `ScopedSignature`; ordered polymorphic terms use `ScopedFamily`. Generic renaming, traversal composition, relational folds, positional reindexing, and semantic renaming for all current polymorphic constructors | General semantic preservation and normalized composition for polymorphic parameter/value substitution remain to be proved |
| Native semantics | One constructor algebra and generic semantic substitution; source preservation composes with resolved lowering | Native fragment is total and monomorphic |
| Recurrence compilation | Prefix uniqueness, least-fixed-point agreement, compact singleton extension and a linear syntax-size theorem | No general termination compiler or evaluation-time certificate |
| Ordered polymorphism | Finite numeric/type/proof syntax, continuous denotation, beta laws, closed embedding, map at finite/infinite lengths, XOR certificate at every finite width | No polymorphic operational adequacy or full upstream `ETAbs`/`ETApp` frontend correspondence |
| Polymorphic recursion | Finite recursive-group syntax, one scheme-environment fixed point, changing-instantiation and mutual-recursion proofs | No general compiler from polymorphic recursive groups to finite native implementations |
| Language semantics | Closed typed core, operational soundness and adequacy, lazy words/sequences, explicit errors | Records, nominal/enumeration types, rational and modular integers, full numeric functions/constraints, full comprehensions, trace/deepseq/random are absent |
| Opaque operations | Unsupported operations are rejected by the importer | Floating point, arrays and foreign backends need explicit semantic interfaces and conditional correspondence proofs |
| Inbound transport | Preserved pinned SHA-256 typed dump, scoped structural reifier, rejection tests and generated-artifact checks | `:extract-coq` erases information; a general typed-AST exporter and Lean decoder remain to be built |
| Outbound transport | Typed resolved printer and comparisons with both pinned evaluators | No formal parser/printer round trip or Haskell correctness proof |
| Foundation | SHA-256 compression for all finite state/block values and valid byte windows; adaptive VCVio replacement | CRC, whole-hash padding and cryptographic security claims remain outside the certificate |

The ordered semantics retains a separate outer result at every numeric and type
quantifier. Flattening all quantifiers into one product of monomorphic
computations would identify distinct demand behaviors. Proof guards are erased
and add no suspension. The generic sort-reindexing API preserves binding
positions under noninjective instantiation; quantified-value semantics is an
additional language-specific responsibility.
