# References

### CRYPTOL360 — Cryptol syntax and reference semantics

Galois, Inc. *Cryptol 3.6.0*.
[Release](https://github.com/GaloisInc/cryptol/releases/tag/3.6.0),
[syntax PDF](https://github.com/GaloisInc/cryptol/blob/3.6.0/docs/Syntax.pdf),
[semantics PDF](https://github.com/GaloisInc/cryptol/blob/3.6.0/docs/Semantics.pdf),
[reference evaluator source](https://github.com/GaloisInc/cryptol/blob/3.6.0/src/Cryptol/Eval/Reference.lhs),
[resolved typed AST](https://github.com/GaloisInc/cryptol/blob/3.6.0/src/Cryptol/TypeCheck/AST.hs).

The semantics document describes lifted value CPOs, suspended product and
sequence components, continuous functions, and recursive declaration groups.
The optional model implements and proves adequacy for a selected resolved
fragment. Its external tests distinguish the reference evaluator from the
normal evaluator, including their negative-integer division discrepancy.

Used in: `Model/`, [model guide](docs/model.md).
