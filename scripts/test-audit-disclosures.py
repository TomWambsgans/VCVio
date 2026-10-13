#!/usr/bin/env python3
"""Regression checks for the audit's security and compatibility disclosures."""

import hashlib
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent


class SecurityDisclosureTests(unittest.TestCase):
    def test_mldsa_query_bounds_are_disclosed_without_statement_changes(self):
        source = (ROOT / "LatticeCrypto/MLDSA/Security.lean").read_text()
        start = source.index("theorem euf_cma_security\n")
        warning = source[source.rfind("/--", 0, start):start]
        self.assertIn("No hypothesis ties the adversary to `qS` or `qH`", warning)
        self.assertIn("placeholder, not the", warning)
        self.assertIn("cited theorem", warning)
        end = source.index("\nend MainTheorem", start)
        self.assertEqual(hashlib.sha256(source[start:end].encode()).hexdigest(),
                         "5728684c0691682d0d0d1b02e1280d22392808e841f19abf216e3d86b2b0f528")


if __name__ == "__main__":
    unittest.main()
