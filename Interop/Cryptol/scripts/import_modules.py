#!/usr/bin/env python3
"""Retain whole modules and report each import stage without conflating them.

The official exporter owns parsing, elaboration and free-variable analysis.
Lean owns decoding and scope/kind validation. This driver records their results
and a declaration graph; it does not infer semantic acceptance from either.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from quote_reference import quote_imperative, quote_imperative_bodies
from export_references import CRYPTOL, FOUNDATION, ROOT, canonical, run, verify_checkout

SELECTED = ("shared/common/utils/List.cry", "shared/CRC/Main.cry")
STAGES = ("expression_typing", "semantic_import", "native_view", "execution",
          "source_correspondence", "property_proof")
OPEN_MODULES = [("list", name) for name in ["Cryptol::Reference"] + [
    "shared::common::utils::" + name for name in ["List", "Sort", "Imperative", "Enum"]]] + [
    ("crc", "shared::CRC::Main")]


def elaborate_module(lean, path, module, *, code=False):
    result = subprocess.run([str(lean), "source", "module-code" if code else "module-elaborate",
                             str(path), module], capture_output=True, text=True, timeout=120)
    report = json.loads(result.stdout)
    if result.returncode and report.get("status") != "rejected":
        raise ValueError(f"module elaborator failed without a diagnostic: {result.stderr}")
    return report


def open_report(lean, artifacts):
    """Attempt every selected whole module, retaining each independent blocker."""
    return {"version": 1, "entries": [
        {"bundle": stem + ".json", "module": module,
         "result": elaborate_module(lean, artifacts / (stem + ".json"), module)}
        for stem, module in OPEN_MODULES]}


def declarations(group):
    return group["args"] if group["tag"] == "nonrecursive" else group["args"][0]


def source_id(module, info):
    """Source identity is independent of bundle-local integer allocation."""
    return {"path": module["provenance"]["path"], "sha256": module["provenance"]["sha256"],
            **info["source_key"]}


def graph(bundle):
    """Resolve dependency edges in this bundle, preserving simultaneous groups."""
    if (bundle["format"], bundle["version"], bundle["cryptol_revision"]) != \
            ("cryptol-module-bundle", 2, CRYPTOL):
        raise ValueError("unsupported module bundle")
    nodes, identities, constructors, parameters = [], {}, {}, {}
    for module in bundle["modules"]:
        metadata = {d["name"]["id"]: d for d in module["declarations"]}
        exported = {e["declaration"]["name"]["id"] for e in module["exports"]}
        for group_index, group in enumerate(module["groups"]):
            for d in declarations(group):
                i = d["name"]["id"]
                if i in identities:
                    raise ValueError(f"duplicate declaration identity: {i}")
                info = metadata[i]
                identity = source_id(module, info)
                identities[i] = identity
                nodes.append({"bundle_id": i, "source": identity, "name": d["name"]["origin"],
                    "module": module["provenance"]["name"], "group": group_index,
                    "recursive_group": group["tag"] == "recursive", "public": i in exported,
                    "property": info["property"], "schema": d["schema"],
                    "definition": d["definition"]["tag"],
                    "dependencies": [n["id"] for n in info["dependencies"]],
                    "stages": {stage: "not-attempted" for stage in STAGES}})
        for nominal in module["nominal_types"]:
            tag, args = nominal["definition"]["tag"], nominal["definition"]["args"]
            names = ([args[0]] if tag == "struct" else
                     [c["name"] for c in args[0]] if tag == "enum" else [])
            for name in names:
                constructors[name["id"]] = name["origin"]
        for parameter in module["value_parameters"]:
            parameters[parameter["name"]["id"]] = parameter["name"]["origin"]
    known = identities.keys() | constructors.keys() | parameters.keys()
    for node in nodes:
        node["unresolved_dependencies"] = sorted(set(node["dependencies"]) - known)
    redirects = {a["id"]: b["id"] for a, b in bundle["primitive_fallbacks"]}
    if any(i not in identities or j not in identities for i, j in redirects.items()):
        raise ValueError("unresolved primitive fallback")
    for node in nodes:
        if node["bundle_id"] in redirects:
            node["reference_fallback"] = redirects[node["bundle_id"]]
    return {"declarations": nodes, "constructors": constructors, "parameters": parameters}


def inspect(exporter, lean, foundation, cryptol, relative):
    path = foundation / relative
    record = {"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    try:
        result = subprocess.run([str(exporter), "--module-bundle", str(foundation), str(path)],
                                capture_output=True, text=True, timeout=120)
        if result.returncode:
            return record | {"frontend": "rejected", "diagnostic": result.stderr.replace(
                str(foundation), "$foundation").strip()}, None
        bundle = json.loads(result.stdout)
        for module in bundle["modules"] + bundle["interfaces"]:
            provenance = module["provenance"]
            source = provenance["path"]
            if source.startswith("$builtin/"):
                actual = cryptol / "lib" / (source[9:].replace("::", "/") + ".cry")
            elif source.startswith("$") or Path(source).is_absolute() or ".." in Path(source).parts:
                raise ValueError(f"unaccounted source path: {source}")
            else:
                actual = foundation / source
            if hashlib.sha256(actual.read_bytes()).hexdigest() != provenance["sha256"]:
                raise ValueError(f"source digest mismatch: {source}")
        # Interfaces can be entry points too; they are retained, not promoted to definitions.
        if not any(m["provenance"]["path"] == relative
                   for m in bundle["modules"] + bundle["interfaces"]):
            raise ValueError("requested module disappeared from the loaded environment")
        data = graph(bundle)
        own = {m["provenance"]["name"] for m in bundle["modules"]
               if m["provenance"]["path"] == relative}
        # Each source owns its declarations. Referenced modules are represented
        # by stable origins, avoiding 135 copies of the entire Prelude graph.
        all_declarations = data["declarations"]
        data["declarations"] = [d for d in all_declarations if d["module"] in own]
        needed = {i for d in data["declarations"] for i in d["dependencies"]}
        data["dependency_origins"] = {d["bundle_id"]: d["source"] for d in all_declarations
                                      if d["bundle_id"] in needed}
        data["constructors"] = {i: n for i, n in data["constructors"].items() if i in needed}
        data["parameters"] = {i: n for i, n in data["parameters"].items() if i in needed}
        with tempfile.TemporaryDirectory(prefix="cryptol-module-") as temporary:
            artifact = Path(temporary) / "module.json"
            artifact.write_bytes(canonical(bundle))
            checked = subprocess.run([str(lean), "source", "modules", str(artifact)],
                                     capture_output=True, text=True, timeout=120)
        report = json.loads(checked.stdout)
        record.update(frontend="accepted", body_retention="exported", graph=data,
                      lean_report=report, lean_exit=checked.returncode)
        if isinstance(report, list):
            record["own_modules"] = sorted(own)
            record["body_retention"] = "decoded"
            record["scope_blockers"] = [r for r in report if r["scope"]["status"] != "accepted"]
        return record, bundle
    except (subprocess.TimeoutExpired, ValueError, KeyError) as error:
        return record | {"pipeline": "failed", "diagnostic": str(error)}, None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--cryptol-source", required=True, type=Path)
    parser.add_argument("--lean", type=Path, default=ROOT.parents[1] / ".lake/build/bin/cryptol-interop")
    parser.add_argument("--all", action="store_true", help="continue across every tracked source")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    verify_checkout(args.cryptol_source, CRYPTOL)
    files = sorted(p for p in run("git", "-C", str(args.foundation), "ls-files").splitlines()
                   if p.endswith(".cry")) if args.all else sorted(SELECTED)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda p: inspect(args.exporter, args.lean, args.foundation,
                                                  args.cryptol_source, p), files))
    output = ROOT / "artifacts/modules"
    output.mkdir(exist_ok=True)

    def write(path, data):
        contents = canonical(data)
        if args.check:
            if path.read_bytes() != contents:
                raise ValueError(f"stale whole-module artifact: {path}")
        else:
            path.write_bytes(contents)

    for path, (record, bundle) in zip(files, results):
        if path in SELECTED and bundle is not None:
            write(output / ("list.json" if path.endswith("List.cry") else "crc.json"), bundle)
            if path.endswith("List.cry"):
                quotation = ROOT / "Bridge/ImperativeSource.lean"
                quoted = quote_imperative(bundle)
                if args.check:
                    if quotation.read_bytes() != quoted:
                        raise ValueError("stale complete Imperative quotation")
                else:
                    quotation.write_bytes(quoted)
    report = {"version": 1, "cryptol_revision": CRYPTOL, "foundation_revision": FOUNDATION,
              "exporter_sha256": hashlib.sha256((ROOT / "exporter/Main.hs").read_bytes()).hexdigest(),
              "entries": [r for r, _ in results]}
    write(output / ("corpus.json" if args.all else "selected.json"), report)
    write(output / "elaboration.json", open_report(args.lean, output))
    utility = json.loads((output / "list.json").read_text())
    typed = elaborate_module(args.lean, output / "list.json",
                             "shared::common::utils::Imperative", code=True)
    quotation = ROOT / "Bridge/ImperativeBodies.lean"
    quoted = quote_imperative_bodies(utility, typed)
    if args.check:
        if quotation.read_bytes() != quoted:
            raise ValueError("stale checked Imperative bodies")
    else:
        quotation.write_bytes(quoted)
    failed = [path for path, (record, _) in zip(files, results)
              if path in SELECTED and record.get("lean_exit") != 0]
    if failed:
        raise ValueError(f"required utility/CRC closure failed: {failed}; corpus report was retained")
    print(json.dumps({"files": len(files), "decoded": sum(r.get("body_retention") == "decoded"
        for r, _ in results), "scoped": sum(r.get("lean_exit") == 0 for r, _ in results)}, sort_keys=True))


if __name__ == "__main__":
    main()
