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

The current development needs the companion PolyFun changes. For a local checkout:

```bash
lake -R -KpolyfunPath=/path/to/PolyFun update PolyFun --keep-toolchain
POLYFUN_PATH=/path/to/PolyFun bash Interop/Cryptol/scripts/validate.sh --lint --test --axioms
```

Keep the resulting local path override out of the committed dependency manifest.
The optional workflow takes an explicit published PolyFun revision.

| Directory | Responsibility | Imports |
|---|---|---|
| `Model` | Types, resolved scoped syntax, lazy domains, operational semantics, adequacy, primitive demand rules | PolyFun, CSLib, Mathlib |
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
The polymorphic-domain spike includes a recursive call at a different numeric
instantiation and distinguishes outer divergence from a returned family with
divergent instances. Its syntax and frontend preservation are not yet integrated.

External evidence uses clean, pinned checkouts:

```bash
CRYPTOL_BINARY=/path/to/cryptol-3.6.0/bin/cryptol \
FOUNDATION_PATH=/path/to/Foundation \
POLYFUN_PATH=/path/to/PolyFun \
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
