#!/usr/bin/env python3
"""Whole-module retention and scope mutations on actual utility/CRC exports."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from import_modules import ROOT, STAGES, elaborate_module, graph, open_report
from quote_reference import quote_imperative, quote_imperative_bodies
from test_source import nodes


def main():
    artifacts = ROOT / "artifacts/modules"
    lean = ROOT.parents[1] / ".lake/build/bin/cryptol-interop"
    bundles = [json.loads((artifacts / (name + ".json")).read_text()) for name in ["list", "crc"]]
    corpus = json.loads((artifacts / "corpus.json").read_text())
    census = json.loads((ROOT / "artifacts/foundation-inventory.json").read_text())
    assert corpus["exporter_sha256"] == hashlib.sha256((ROOT / "exporter/Main.hs").read_bytes()).hexdigest()
    assert [e["path"] for e in corpus["entries"]] == [e["path"] for e in census["entries"]]
    public = [d for e in corpus["entries"] for d in e["graph"]["declarations"] if d["public"]]
    expected = [d for e in census["entries"] for m in e.get("modules", []) for d in m["exports"]]
    assert len(public) == len(expected)
    assert sum(d["property"] for d in public) == sum(d["property"] for d in expected)
    assert all(d["stages"] == {s: "not-attempted" for s in STAGES}
               for e in corpus["entries"] for d in e["graph"]["declarations"])

    def check(bundle):
        with tempfile.TemporaryDirectory(prefix="cryptol-module-test-") as temporary:
            path = Path(temporary) / "module.json"
            path.write_text(json.dumps(bundle))
            result = subprocess.run([str(lean), "source", "modules", str(path)],
                                    capture_output=True, text=True, timeout=60)
            return result.returncode, json.loads(result.stdout)

    for bundle in bundles:
        code, report = check(bundle)
        assert code == 0 and all(r["scope"]["status"] == "accepted" for r in report), report
        assert all(r["semantic_import"] == "not-attempted" for r in report)
        assert not any(d["unresolved_dependencies"] for d in graph(bundle)["declarations"])
        reference = next(m for m in bundle["modules"]
                         if m["provenance"]["name"] == "Cryptol::Reference")
        assert {"pmult", "pdiv", "pmod", "foldl", "foldWhile", "scanl", "iterate"} <= {
            e["declaration"]["name"]["text"] for e in reference["exports"]}
    utility, crc = bundles
    assert json.loads((artifacts / "elaboration.json").read_text()) == open_report(lean, artifacts)
    assert (ROOT / "Bridge/ImperativeSource.lean").read_bytes() == quote_imperative(utility)
    imperative_name = "shared::common::utils::Imperative"
    typed = elaborate_module(lean, artifacts / "list.json", imperative_name, code=True)
    assert typed["expression_typing"] == "accepted" and typed["shared_declarations"] == 2
    assert typed["source_correspondence"] == "not-established"
    assert (ROOT / "Bridge/ImperativeBodies.lean").read_bytes() == quote_imperative_bodies(utility, typed)

    def mutate_imperative(type_preserving):
        mutant = deepcopy(utility)
        module = next(m for m in mutant["modules"] if m["provenance"]["name"] == imperative_name)
        condition = next(n for n in nodes(module["groups"]) if n.get("tag") == "if")
        if type_preserving:
            # Returning the initial state has the right polymorphic type but changes the loop.
            replacement = deepcopy(condition["args"][2])
            condition.clear()
            condition.update(replacement)
        else:
            # A type parameter cannot be used as Bit; this still passes scope/kind checking.
            condition["args"][0] = deepcopy(condition["args"][2])
        assert check(mutant)[0] == 0
        with tempfile.TemporaryDirectory(prefix="cryptol-typed-module-") as temporary:
            path = Path(temporary) / "mutant.json"
            path.write_text(json.dumps(mutant))
            return elaborate_module(lean, path, imperative_name, code=True)

    rejected = mutate_imperative(False)
    assert rejected["status"] == "rejected" and "scheme mismatch" in rejected["message"], rejected
    changed = mutate_imperative(True)
    assert changed["expression_typing"] == "accepted" and changed["bodies"] != typed["bodies"]
    modules = {m["provenance"]["name"]: m for m in utility["modules"]}
    assert all("shared::common::utils::" + name in modules
               for name in ["List", "Sort", "Enum", "Imperative"])
    assert any(n.get("tag") == "case" for n in nodes(utility))
    crc_module = next(m for m in crc["modules"] if m["provenance"]["name"] == "shared::CRC::Main")
    assert len(crc_module["type_parameters"]) == 1 and len(crc_module["value_parameters"]) == 7
    assert {"CRCUpdate", "CRCRunning"} <= {
        e["declaration"]["name"]["text"] for e in crc_module["exports"]}

    def remove_parameter(bundle):
        next(m for m in bundle["modules"] if m["provenance"]["name"] ==
             "shared::CRC::Main")["value_parameters"] = []

    def corrupt_body(bundle):
        # Mutate retained groups, not the redundant export display copy.
        module = next(m for m in bundle["modules"] if m["provenance"]["name"] ==
                      "shared::common::utils::Enum")
        node = next(n for n in nodes(module["groups"]) if n.get("tag") == "case")
        node["args"][1].append(deepcopy(node["args"][1][0]))

    def nominal_in_body(bundle):
        module = next(m for m in bundle["modules"] if m["provenance"]["name"] ==
                      "shared::common::utils::List")
        node = next(n for n in nodes(module["groups"]) if n.get("tag") == "nominal")
        node["args"][0]["id"] = 99999999

    mutations = [
        (utility, nominal_in_body), (utility, corrupt_body), (crc, remove_parameter),
        (utility, lambda b: b["primitive_fallbacks"][0][1].update(id=99999999)),
        (utility, lambda b: b.update(cryptol_revision="untrusted")),
        (utility, lambda b: b["modules"][0]["provenance"].update(path="../escape.cry")),
        (utility, lambda b: b["modules"][0].update(declarations=[])),
    ]
    for original, mutate in mutations:
        mutant = deepcopy(original)
        mutate(mutant)
        code, report = check(mutant)
        assert code != 0, report
        if isinstance(report, list):
            assert len(report) == len(mutant["modules"]), "validation stopped at first failure"
    print(f"Whole modules: utility/CRC retention, 6 typed attempts, complete Imperative import, "
          f"{len(mutations)} scope mutations and 2 typing/meaning mutations")


if __name__ == "__main__":
    main()
