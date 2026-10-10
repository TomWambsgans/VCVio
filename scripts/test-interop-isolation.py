#!/usr/bin/env python3
"""Exercise each Cryptol import boundary, including Lean import modifiers."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class IsolationTests(unittest.TestCase):
    def check(self, files):
        with tempfile.TemporaryDirectory(prefix="vcvio-interop-isolation-") as temp:
            root = Path(temp)
            (root / "scripts").mkdir()
            shutil.copyfile(Path(__file__).with_name("check-interop-isolation.sh"),
                            root / "scripts/check-interop-isolation.sh")
            for name, source in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            return subprocess.run(["bash", "scripts/check-interop-isolation.sh"], cwd=root,
                                  text=True, capture_output=True, timeout=10)

    def test_forbidden_edges_and_modifiers(self):
        edges = [("HashSig/X.lean", "Interop.Cryptol.Bridge"),
                 ("VCVio.lean", "Interop.Cryptol.Model"),
                 ("VCVioTest/X.lean", "Hax"),
                 ("Interop/Cryptol/Model/X.lean", "Interop.Cryptol.Translation"),
                 ("Interop/Cryptol/Translation/X.lean", "HashSig"),
                 ("Interop/Cryptol/Translation/X.lean", "Interop.Cryptol.Bridge.X"),
                 ("Interop/Cryptol/Bridge/X.lean", "Interop.Hax"),
                 ("Interop/Hax/X.lean", "Interop.Cryptol.Model"),
                 ("Interop/Cryptol/Model/X.lean", "VCVio")]
        for source, target in edges:
            for modifier in ("import", "public import", "import all", "public meta import", "public/-comment-/import",
                             "public\nimport", "import\n"):
                with self.subTest(source=source, target=target, modifier=modifier):
                    result = self.check({source: f"module\n{modifier} {target}\n"})
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(f"forbidden import {target}", result.stderr)

    def test_allowed_edges_comments_and_multiple_imports(self):
        result = self.check({
            "Interop/Cryptol/Model/X.lean": "public import PolyFun Cslib\n"
                "/- outer /- nested -/ public import VCVio -/\n-- import HashSig\n",
            "Interop/Cryptol/Translation/X.lean": "import Interop.Cryptol.Model.X\n",
            "Interop/Cryptol/Bridge/X.lean": "import HashSig VCVio Interop.Cryptol.Translation.X\n",
            "Interop/Cryptol/Consumer/Consumer.lean": "import Interop.Cryptol.Bridge\n",
            "Interop/Cryptol/Consumer/lakefile.lean": "import Lake\n",
            "Interop/Hax/X.lean": "import VCVio ToMathlib\n",
            "HashSig/X.lean": "import VCVio\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = self.check({"HashSig/X.lean": "import Mathlib Interop.Cryptol.Model\n"})
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
