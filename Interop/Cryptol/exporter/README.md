# Pinned Cryptol typed-AST exporter

This executable links Cryptol 3.6.0 at commit
`61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`, with an explicitly identified optional
case-binder compatibility patch. It exports full dependency closures
from the official typed AST, retaining ordered type/proof binders, schemes,
recursive declaration groups, guards, comprehension branches, and foreign
fallback bodies. It also retains the official `Cryptol::Reference` fallback
definitions for polynomial arithmetic and folds/scans. Locations on expressions
are currently erased; declaration identities and module content hashes remain.

The supported build uses GHC 9.6.7 and Cabal 3.12.1.0. `cabal.project.freeze`
records the resolved dependencies and Hackage index state. Z3 must be on `PATH`
for the frontend's type checker. The executable is threaded because Cryptol's
solver process needs the threaded Haskell runtime.

```bash
cd Interop/Cryptol/exporter
cabal build cryptol-lean-export
cabal list-bin cryptol-lean-export
```

From the repository root, after `lake build cryptol-interop`:

```bash
python3 Interop/Cryptol/scripts/export_references.py \
  --exporter /path/to/cryptol-lean-export \
  --foundation /path/to/pinned/Foundation \
  --cryptol-source /path/to/pinned/cryptol
```

Add `--check` to require byte-identical committed artifacts. The driver checks
the Foundation revision and exact frontend revision/patch identity, all loaded module digests,
2,020 numeric cases
against `InfNat`, 345 class/literal cases against the official class solver,
and Lean scope/kind validation. Temporary entry modules do not modify Foundation.

The checked corpus contains 31 roots and 280 shared declarations: SHA256
compression, six complete SHA2 hashes, four SHA3 hashes, four SHAKE/RawSHAKE
functions, six Keccak/state-conversion entries, six AES functions, and four CRC
entries. `artifacts/references/manifest.json` maps catalogue IDs to entry roots.
The JSON contains definitions and dependency edges, not output-vector stubs.

`source inspect` reports **scoped**. This establishes neither expression typing
nor semantic correctness of the Haskell frontend/exporter. The full source
graph still needs checked elaboration, a shared executable evaluator, and a
correspondence theorem before it can supply broader semantic certificates.
The existing SHA256 compression certificate uses its separately checked path.

The driver also exports the seven-declaration closure for
`(sigma_256_0 : [32] -> [32])` to `scalar-bundle.json` and quotes its constructors
into `Bridge/ImportedScalarSource.lean`. The quote generator does no semantic
normalization. `source elaborate …/scalar-bundle.json` reports **typed**, with
the checked resolved expression. `Bridge.ImportedScalar.accepted` verifies that
exact output in the kernel, and `core_correct` relates it to core `Sha2.ssig0`
on every 32-bit input. Its deliberately small elaboration fragment rejects
unsupported syntax and primitives; general frontend semantic preservation is
still a separate obligation. Both additional artifacts have manifest digests
and participate in byte-identical regeneration and negative typing tests.

`ImportedScalar.compiled` retains the finite native IR with a correctness
certificate for this exact imported source. `core_contract_iff` transfers
arbitrary bitvector pre/postconditions to core `Sha2.ssig0` through the shared
PolyFun correspondence machinery.

To include regeneration in optional external validation, set `CRYPTOL_EXPORTER`
and `CRYPTOL_SOURCE` alongside `CRYPTOL_BINARY` and `FOUNDATION_PATH`. Ordinary
validation checks the committed artifacts and all rejection cases without GHC,
Cabal, Cryptol, or network access.

## Official transformation candidates and complete module discovery

`cryptol-lean-export --specialize FOUNDATION MODULE ROOT...` returns the original
bundle and an untrusted specialization candidate. It invokes the official
`Specialize.specializeEWhere` API while keeping primitive instantiations explicit;
the convenience specializer loses arguments from cloned primitives. The committed
`specialized-scalar-bundle.json` is quoted without semantic processing, accepted
by the Lean importer and related to the original scalar by
`ImportedSpecialization.correct`. Reusing its native implementation requires that
proof. A same-typed rotation mutation fails the kernel certificate.

`cryptol-lean-export --module FOUNDATION MODULE` uses the official loader to
export public declarations, property pragmas, parameters, interfaces, module
provenance and declaration locations. Run the census with:

```bash
python3 Interop/Cryptol/scripts/inventory_foundation.py \
  --exporter /path/to/cryptol-lean-export --foundation /path/to/pinned/Foundation
```

`--check` requires byte-identical reproduction. All 135 tracked files are covered;
export success is separate from typing, semantic and native-equivalence stages.
The [integration report](../docs/tooling.md) explains the architecture and gaps.
The same reference regeneration driver quotes nine local language canaries,
including records, lexical capture, higher-order functions and infinite mapping.

## Whole-module bundles

`cryptol-lean-export --module-bundle FOUNDATION MODULE` emits version 3 of
`cryptol-module-bundle`. It preserves private declarations, simultaneous groups,
module parameters, type synonyms, nominal definitions and case alternatives.
Reference fallback definitions are loaded through Cryptol's internal loader
without resetting the requested module's environment. Foreign interfaces have
canonical ABI metadata, without checkout paths from compiler debug output.

```bash
python3 Interop/Cryptol/scripts/import_modules.py --all \
  --exporter /path/to/cryptol-lean-export --foundation /path/to/pinned/Foundation \
  --cryptol-source /path/to/pinned/cryptol
```

This continues after individual failures and writes the full declaration queue
and separate stage results, including linking and typed elaboration of every
owned module instance. Add `--check` for byte-identical regeneration. All 135 files
pass scope/kind checks with the compatibility frontend, and all 155 owned module
instances link. Complete semantic import, generated native interfaces and source
preservation remain separate unfinished gates; see the
[compatibility report](../docs/compatibility.md).

## Building the identified compatibility frontend

Keep the original pinned checkout available. Create a separate worktree at the
same revision and apply `patches/case-binder-types.patch` there. In a local Cabal
project, name that checkout and this exporter as `packages`, retain Cryptol's
`-ffi -relocatable` flags, and add:

```cabal
package cryptol-lean-export
  flags: +case-binder-types
```

`python3 Interop/Cryptol/scripts/frontend.py /path/to/compatibility/cryptol`
checks that the tracked diff is exactly the committed patch and prints its
identity. The digest identifies the canonical Git diff; the stored patch omits
space prefixes on empty context lines to avoid trailing whitespace (Git accepts
both representations). The exporter records that digest in `frontend_patches`. The export
drivers reject a flag/source mismatch or any other source modification. The
default Cabal project still builds the unmodified pin with an empty patch list;
that frontend retains the known case-annotation failure. Constructor tags use
exhaustive explicit matches, independent of upstream `Show` formatting.

This provenance check does not verify Haskell or prove which source produced
an arbitrary binary. The identified frontend and serializer remain external
assumptions; Lean checks the exact artifact it receives. The negative fixture
`artifacts/regressions/case-binder-unpatched.json` is copied from the unmodified
frontend and is not repaired by the Lean checker.
