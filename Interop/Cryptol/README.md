# Cryptol interoperability

This optional development connects resolved Cryptol descriptions, a lazy Lean
semantics, total native implementations, and VCVio specifications. It shares
VCVio's root toolchain and dependency manifest. The specification target is
Cryptol **3.6.0's reference evaluator**; normal-evaluator differences are recorded
in the [model guide](docs/model.md).

Run commands from the VCVio repository root:

```bash
lake build CryptolModel CryptolTranslation CryptolBridge CryptolTests --wfail
lake build cryptol-interop
lake exe cryptol-interop model run productive_stream
lake exe cryptol-interop model arx-native 32 8
./scripts/validate.sh --cryptol --lint --test --axioms
```

The root manifest pins the companion PolyFun development at
`9a7e7f78ab2567d4c3c98629a13d31e10726bae1`. The commands above and the separate
`Consumer` use that published dependency; no sibling checkout is required.
For local development against a different PolyFun checkout:

```bash
lake -R -KpolyfunPath=/path/to/PolyFun update PolyFun --keep-toolchain
POLYFUN_PATH=/path/to/PolyFun bash Interop/Cryptol/scripts/validate.sh --lint --test --axioms
```

Keep the resulting local path override out of the committed dependency manifest.
The optional workflow runs on PR changes affecting this project and uses the
committed PolyFun pin by default. Manual and reusable invocations can supply
`polyfun_ref` to check a companion revision. External Cryptol and Foundation
comparisons remain an explicit local validation option.

| Directory | Responsibility | Imports |
|---|---|---|
| `Model` | Types, resolved and ordered polymorphic syntax, lazy domains, monomorphic operational semantics and adequacy, primitive demand rules | PolyFun, CSLib, Mathlib |
| `Translation` | Native scoped IR, representation relation, source translation, certificates, quotation and export | Model |
| `Bridge` | Foundation source artifacts, SHA-256 correspondence, byte encoding and VCVio probability theorems | Model, Translation, VCVio, HashSig |
| `Tests` | Public API, semantic and rejection regressions | The three optional libraries |
| `Consumer` | A separate ordinary-import consumer using the root toolchain and dependencies | The public APIs |

Default VCVio libraries and tests do not import Cryptol. The dormant Rust/hax/aeneas
aggregate remains separate. The isolation checker enforces each direction.
The three generated umbrellas are maintained by `scripts/update-lib.sh` after
new modules have been staged.

Both resolved source and the native IR are PolyFun scoped polynomial trees.
Variables are leaves; operations describe child types and their binders.
Renaming, substitution, interpretation and their general laws live upstream.
Native lowering has one semantic route: native IR → resolved source → core.
A source certificate then transports arbitrary pre/postconditions, and the bridge
connects the certified compression function to VCVio's byte implementation and
adaptive oracle clients. See the [model guide](docs/model.md) and
[Foundation guide](docs/foundation.md) for the precise claims.

The native prefix builder binds both the prefix and the newly computed entry,
then stores a prefix reference and a single append node.
`Term.nodeCount_prefixTable_le` proves a linear description-size bound when step
bodies have a uniform size bound. This is not an evaluation-time bound.
Ordered numeric, type, and proof binders use PolyFun's context-changing binding
families. One finite syntax tree denotes polymorphic map at finite or infinite
lengths; another supplies XOR with a representation certificate for every finite
width, including zero. Recursive groups take a single fixed point before
instantiation. The semantics distinguishes errors at successive quantifiers,
outer divergence, and a returned family with divergent instances.

Public beta laws, the closed resolved embedding, and per-instance specification
transfer are proved. General semantic preservation of polymorphic syntax
substitution, polymorphic operational adequacy, and frontend correspondence
remain open. The existing monomorphic adequacy theorem keeps its original scope.

External evidence uses clean, pinned checkouts:

```bash
CRYPTOL_BINARY=/path/to/cryptol-3.6.0/bin/cryptol \
FOUNDATION_PATH=/path/to/Foundation \
  bash Interop/Cryptol/scripts/validate.sh --lint --test --axioms --external
```

Foundation is pinned to `7d0528bd998682788f4e23661f2829298f9e47db`; the extraction
manifest records files, identities and hashes. Validation does not download or
install these tools.

The current fragment is intentionally narrower than full resolved Cryptol.
The [coverage and gap ledger](docs/model.md#coverage-and-gap-ledger) separates
proved capabilities, semantic spikes, and missing language features. In particular,
the importer still targets the Foundation SHA-256 subset; no general typed-AST
exporter, full Cryptol soundness theorem, or CRC certificate is claimed.
