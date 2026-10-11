"""Validate the reference-corpus inventory separately from semantic certification."""

from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tempfile

import extract_foundation as extract

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError("coverage catalogue: " + message)


def safe_path(text):
    require(isinstance(text, str), "path must be text")
    path = PurePosixPath(text)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == text,
            "noncanonical relative path: " + text)
    return path


def validate(data, root=ROOT):
    require(data.get("schema_version") == 1, "unknown schema version")
    manifest = json.loads((root / "artifacts/manifest.json").read_text())
    for key in ("foundation_revision", "cryptol_revision"):
        require(data.get(key) == manifest[key], key + " differs from extraction pin")
    entries = data.get("entries")
    require(isinstance(entries, list) and entries, "empty entry list")
    features, profiles = data.get("features", {}), data.get("profiles", {})
    require(features and profiles and all(isinstance(s, str) and s for s in
            [*features.values(), *profiles.values()]), "missing feature/profile definitions")
    hashes = data.get("source_sha256", {})
    for path, digest in hashes.items():
        require(safe_path(path).suffix == ".cry", "non-Cryptol source")
        require(isinstance(digest, str) and re.fullmatch(r"[a-f0-9]{64}", digest),
                "invalid source digest")
    canary = (root / "Tests/Bridge/Coverage.lean").read_text()
    declarations = set(re.findall(r"^example := ([A-Za-z_][\w.]*)$", canary, re.MULTILINE))
    ids, required_declarations = set(), set()
    for entry in entries:
        key = entry.get("id")
        require(isinstance(key, str) and re.fullmatch(r"[a-z0-9_-]+", key), "invalid entry id")
        require(key not in ids, "duplicate entry: " + key)
        ids.add(key)
        require(entry.get("profile") in profiles, key + ": unknown profile")
        required = entry.get("required_features")
        require(isinstance(required, list) and required and set(required) <= features.keys(),
                key + ": unknown or empty feature requirements")
        source = entry.get("source", {})
        require(source.get("module") in hashes, key + ": source module is not pinned")
        require(isinstance(source.get("symbol"), str) and
                re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.:]*", source["symbol"]),
                key + ": invalid public symbol")
        require(source.get("probe") in (None, "compression-wrapper"), key + ": unknown type probe")
        dependencies = entry.get("dependencies", {})
        if dependencies.get("status") == "extracted":
            require(dependencies.get("manifest") == "artifacts/manifest.json" and
                    isinstance(manifest.get(dependencies.get("key")), list) and
                    manifest[dependencies["key"]], key + ": missing extracted closure")
        else:
            require(dependencies.get("status") == "partial", key + ": unknown dependency status")
            require(set(dependencies.get("modules", [])) <= hashes.keys(), key + ": unpinned dependency")
        status = entry.get("status")
        require(status in {"planned", "probe", "certified"}, key + ": unknown proof strength")
        theorems = entry.get("theorems", [])
        evidence = entry.get("evidence", [])
        trusted = entry.get("trusted_steps", [])
        require(isinstance(theorems, list) and isinstance(evidence, list) and isinstance(trusted, list),
                key + ": invalid evidence lists")
        if status == "certified":
            require(theorems and trusted and entry.get("implementation"),
                    key + ": certificate needs theorem, implementation and trust boundary")
        else:
            require(not theorems and not trusted, key + ": uncertified entry claims a certificate")
        require(status != "probe" or evidence, key + ": probe has no evidence")
        for path in evidence:
            require((root / str(safe_path(path))).is_file(), key + ": missing evidence file")
        names = theorems + ([entry["implementation"]] if entry.get("implementation") else [])
        require(all(isinstance(name, str) and name in declarations for name in names),
                key + ": declaration lacks a compiled ordinary-import check")
        required_declarations.update(names)
    require(required_declarations == declarations, "declaration checks drifted from the catalogue")
    return {"entries": len(entries), "families": sorted({e["family"] for e in entries}),
            "statuses": dict(sorted(Counter(e["status"] for e in entries).items())),
            "source_modules": len(hashes), "declarations": len(declarations)}


def rejection_checks(data):
    """A status change or broken provenance cannot silently count as coverage."""
    mutants = []
    m = deepcopy(data); m["entries"].append(deepcopy(m["entries"][0])); mutants.append(m)
    m = deepcopy(data); m["foundation_revision"] = "0" * 40; mutants.append(m)
    m = deepcopy(data); m["entries"][1]["status"] = "certified"; mutants.append(m)
    m = deepcopy(data); m["entries"][0]["theorems"] = []; mutants.append(m)
    m = deepcopy(data); m["entries"][0]["theorems"] = ["Bogus.proof"]; mutants.append(m)
    m = deepcopy(data); m["entries"][0]["profile"] = "unrestricted"; mutants.append(m)
    m = deepcopy(data); m["entries"][0]["required_features"] = ["missing"]; mutants.append(m)
    m = deepcopy(data); m["entries"][0]["evidence"] = ["../README.md"]; mutants.append(m)
    for mutant in mutants:
        try:
            validate(mutant)
        except ValueError:
            continue
        raise AssertionError("invalid coverage metadata accepted")
    return len(mutants)


def check(cryptol=None, foundation=None):
    data = json.loads((ROOT / "coverage.json").read_text())
    report = validate(data)
    report["metadata_rejections"] = rejection_checks(data)
    if cryptol is None:
        return report
    # Every inventoried source is checked by content, including partial dependency lists.
    for path, digest in data["source_sha256"].items():
        require(hashlib.sha256((foundation / path).read_bytes()).hexdigest() == digest,
                "source changed: " + path)
    modules = defaultdict(list)
    for entry in data["entries"]:
        modules[entry["source"]["module"]].append(entry)
    checked = 0
    with tempfile.TemporaryDirectory(prefix="cryptol-corpus-") as temporary:
        wrapper = Path(temporary) / "PolyFunCompression.cry"
        wrapper.write_text(extract.COMPRESSION)
        for module, entries in sorted(modules.items()):
            ordinary = [e for e in entries if not e["source"].get("probe")]
            if ordinary:
                output = extract.run(cryptol, foundation,
                    [f":load {module}", *[":type " + e["source"]["symbol"] for e in ordinary]])
                require(output.strip(), "no type output: " + module)
                checked += len(ordinary)
            for entry in entries:
                if entry["source"].get("probe"):
                    output = extract.run(cryptol, foundation, [f":load {wrapper}", ":type result"])
                    require("[8][32]" in output and "[16][32]" in output,
                            "compression profile type changed")
                    checked += 1
    report["externally_typed_entries"] = checked
    report["external_meaning"] = "Frontend type probes and source hashes; no semantic certificate implied"
    return report
