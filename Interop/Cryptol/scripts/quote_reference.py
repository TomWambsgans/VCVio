"""Quote raw typed-AST data for kernel-checked import certificates.

This module performs constructor serialization only. It does not specialize,
type-check, normalize, or compile a source expression. export_references.py owns
regeneration and byte-for-byte checks against the pinned Haskell export.
"""

import json
import re


def string(value):
    return json.dumps(value, ensure_ascii=False)


def array(values):
    return "[" + ", ".join(values) + "]"


def app(constructor, *arguments):
    return "(" + constructor + (" " if arguments else "") + " ".join(arguments) + ")"


def name(value):
    return app("Reference.Name.mk", str(value["id"]), string(value["text"]),
               string(value["origin"]))


def parameter(value):
    kind = {"num": "number", "type": "value", "prop": "proposition"}[value["kind"]["tag"]]
    return app("Reference.Parameter.mk", str(value["id"]), "." + kind)


def type_expr(value):
    tag, args = value["tag"], value["args"]
    if tag == "var":
        return app(".var", parameter(args[0]))
    if tag == "num":
        return app(".number", str(int(args[0])))
    if tag == "con":
        return app(".constructor", string(args[0]), array(map(type_expr, args[1])))
    if tag == "synonym":
        return app(".synonym", name(args[0]), array(map(type_expr, args[1])), type_expr(args[2]))
    if tag == "nominal":
        return app(".nominal", name(args[0]), array(map(type_expr, args[1])))
    if tag == "tuple":
        return app(".tuple", str(args[0]), array(map(type_expr, args[1])))
    if tag == "record":
        return app(".record", array(app("Prod.mk", string(k), type_expr(t)) for k, t in args[0]))
    if tag == "has":
        return app(".has", selector(args[0]), array(map(type_expr, args[1])))
    raise ValueError(f"unhandled raw type constructor: {tag}")


def schema(value):
    return app("Reference.Schema.mk", array(map(parameter, value["parameters"])),
               array(map(type_expr, value["constraints"])), type_expr(value["body"]))


def selector(value):
    tag, (index, shape) = value["tag"], value["args"]
    if tag == "record":
        return app(".record", string(index), ".none" if shape is None else
                   app(".some", array(map(string, shape))))
    if tag in {"tuple", "list"}:
        return app("." + tag, str(index), ".none" if shape is None else app(".some", str(shape)))
    raise ValueError(f"unhandled selector: {tag}")


def expression(value):
    tag, args = value["tag"], value["args"]
    if tag == "var":
        return app(".var", name(args[0]))
    if tag == "app":
        return app(".app", expression(args[0]), expression(args[1]))
    if tag == "abs":
        return app(".abs", name(args[0]), type_expr(args[1]), expression(args[2]))
    if tag == "typeAbs":
        return app(".typeAbs", parameter(args[0]), expression(args[1]))
    if tag == "typeApp":
        return app(".typeApp", expression(args[0]), type_expr(args[1]))
    if tag == "proofAbs":
        return app(".proofAbs", type_expr(args[0]), expression(args[1]))
    if tag == "proofApp":
        return app(".proofApp", expression(args[0]))
    if tag == "where":
        return app(".whereE", expression(args[0]), array(map(group, args[1])))
    if tag == "list":
        return app(".list", type_expr(args[0]), array(map(expression, args[1])))
    if tag == "if":
        return app(".ite", *map(expression, args))
    if tag == "case":
        return app(".caseE", expression(args[0]), array(
            app("Prod.mk", string(k), case_alt(a)) for k, a in args[1]),
            ".none" if args[2] is None else app(".some", case_alt(args[2])))
    if tag == "update":
        return app(".update", type_expr(args[0]), expression(args[1]),
                   selector(args[2]), expression(args[3]))
    if tag == "guards":
        return app(".guards", type_expr(args[0]), array(
            app("Prod.mk", array(map(type_expr, cs)), expression(e)) for cs, e in args[1]))
    if tag == "tuple":
        return app(".tuple", array(map(expression, args[0])))
    if tag == "record":
        return app(".record", array(app("Prod.mk", string(k), expression(e)) for k, e in args[0]))
    if tag == "select":
        return app(".select", expression(args[0]), selector(args[1]))
    if tag == "comprehension":
        return app(".comprehension", type_expr(args[0]), type_expr(args[1]), expression(args[2]),
                   array(array(map(match_expr, branch)) for branch in args[3]))
    raise ValueError(f"unhandled raw expression constructor: {tag}")


def case_alt(value):
    return app("Reference.CaseAlt.mk", array(
        app("Prod.mk", name(n), type_expr(t)) for n, t in value["bindings"]),
        expression(value["body"]))


def match_expr(value):
    tag, args = value["tag"], value["args"]
    if tag == "from":
        return app(".from", name(args[0]), type_expr(args[1]), type_expr(args[2]), expression(args[3]))
    if tag == "let":
        return app(".letE", declaration(args[0]))
    raise ValueError(f"unhandled match: {tag}")


def declaration(value):
    definition = value["definition"]
    if definition["tag"] == "primitive":
        body = ".primitive"
    elif definition["tag"] == "expression":
        body = app(".expression", expression(definition["args"][0]))
    elif definition["tag"] == "foreign":
        interface, fallback = definition["args"]
        body = app(".foreign", string(interface), ".none" if fallback is None else
                   app(".some", expression(fallback)))
    else:
        raise ValueError("unsupported raw declaration form")
    return app("Reference.Decl.mk", name(value["name"]), schema(value["schema"]), body)


def group(value):
    if value["tag"] == "nonrecursive":
        return app(".nonrecursive", declaration(value["args"][0]))
    if value["tag"] == "recursive":
        return app(".recursive", array(map(declaration, value["args"][0])))
    raise ValueError("unsupported declaration group")


def wrap(source):
    # String literals stay indivisible; layout is otherwise irrelevant inside parentheses.
    tokens = re.findall(r'"(?:\\.|[^"\\])*"|[^\s"]+', source)
    lines, line = [], "  "
    for token in tokens:
        if len(line) + len(token) + 1 > 98 and line.strip():
            lines.append(line.rstrip())
            line = "  "
        line += token + " "
    return "\n".join(lines + [line.rstrip()])


def quote_bundle(bundle, *, namespace="ImportedScalarSource", artifact="scalar-bundle.json",
                 title="Quoted Foundation scalar source"):
    assert bundle["roots"] and not bundle["primitive_fallbacks"]
    declarations = []
    for group in bundle["groups"]:
        assert group["tag"] == "nonrecursive"
        declarations.append(declaration(group["args"][0]))
    modules = [app("SourceModule.mk", string(m["name"]), string(m["path"]),
                   string(m["sha256"]), array(app("Prod.mk", name(n), string(a))
                                             for n, a in m["aliases"])) for m in bundle["modules"]]
    source = '''/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# Quoted Foundation scalar source

Raw constructor data from `artifacts/references/scalar-bundle.json`, including
source identities, schemes and annotations. `Interop/Cryptol/scripts/export_references.py`
checks byte-for-byte reproduction from the pinned official frontend.
-/

public section

namespace Cryptol.Bridge.ImportedScalarSource

open Cryptol Translation

'''
    for i, d in enumerate(declarations):
        source += f'/-- Source declaration {i + 1} in dependency order. -/\n'
        source += f'@[expose] def declaration{i} : Reference.Decl :=\n{wrap(d)}\n\n'
    roots = []
    for i, root in enumerate(bundle['roots']):
        roots.append('root' if len(bundle['roots']) == 1 else f'root{i}')
        source += '/-- The official frontend\'s fully instantiated entry point. -/\n'
        source += f'@[expose] def {roots[-1]} : SourceRoot :=\n' + wrap(app(
            'SourceRoot.mk', string(root['text']), expression(root['expression']),
            schema(root['schema']))) + '\n\n'
    groups = array(app('.nonrecursive', f'declaration{i}') for i in range(len(declarations)))
    source += '/-- The exact exported scalar bundle, retaining its provenance metadata. -/\n'
    source += '@[expose] def bundle : SourceBundle :=\n' + wrap(app(
        'SourceBundle.mk', string(bundle['cryptol_revision']), array(roots), groups,
        array(modules), '[]', array(map(string, bundle.get('frontend_patches', []))))) + '\n\nend Cryptol.Bridge.ImportedScalarSource\n'
    source = source.replace("ImportedScalarSource", namespace)
    source = source.replace("scalar-bundle.json", artifact)
    source = source.replace("Quoted Foundation scalar source", title)
    return source.encode()


def source_module(value):
    return app("SourceModule.mk", string(value["name"]), string(value["path"]),
               string(value["sha256"]), array(app("Prod.mk", name(n), string(a))
                                             for n, a in value["aliases"]))


def source_location(value):
    pair = lambda xs: app("Prod.mk", *map(str, xs))
    return app("SourceLocation.mk", string(value["source_basename"]),
               pair(value["start"]), pair(value["end"]))


def declaration_info(value):
    key = value["source_key"]
    identity = app("SourceIdentity.mk", ".none" if key["module"] is None else
                   app(".some", string(key["module"])), string(key["name"]),
                   source_location(key["location"]))
    return app("DeclarationInfo.mk", name(value["name"]), identity,
               array(map(name, value["dependencies"])), str(value["property"]).lower())


def quote_imperative(bundle):
    """Quote every retained field of the dependency-closed Imperative module."""
    module = next(m for m in bundle["modules"]
                  if m["provenance"]["name"] == "shared::common::utils::Imperative")
    empty = ("type_parameters", "value_parameters", "constraints", "type_exports",
             "nominal_exports", "type_synonyms", "nominal_types", "nested_functors",
             "nested_signatures")
    if any(module[key] for key in empty):
        raise ValueError("Imperative module shape changed; extend quotation before regenerating")
    own_names = [d["name"] for d in module["declarations"]]
    if any(n not in own_names for d in module["declarations"] for n in d["dependencies"]):
        raise ValueError("Imperative acquired an external dependency; retain its closure")
    groups = array(map(group, module["groups"]))
    source = app("ModuleDefinition.mk", source_module(module["provenance"]), "[]", "[]", "[]",
                 array(name(e["declaration"]["name"]) for e in module["exports"]), "[]", "[]",
                 "[]", "[]", groups, array(map(declaration_info, module["declarations"])),
                 "[]", "[]")
    return ('''/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# Retained Foundation imperative utilities

Exact constructor quotation of the complete `Imperative` module in
`artifacts/modules/list.json`. The module has no external value dependencies.
`Interop/Cryptol/scripts/import_modules.py` reproduces every retained field
from the pinned official frontend export.
-/

public section

namespace Cryptol.Bridge.ImperativeSource

open Translation

/-- Complete source module, including both exported bodies and their source identities. -/
@[expose] def source : ModuleDefinition :=
''' + wrap(source) + '''

/-- The dependency-closed module bundle used by the checked open importer. -/
@[expose] def bundle : ModuleBundle :=
  ⟨SourceBundle.expectedCryptolRevision, [source], [], [],
    ''' +
        array(map(string, bundle.get('frontend_patches', []))) + '''⟩

end Cryptol.Bridge.ImperativeSource
''').encode()


def quote_imperative_bodies(bundle, checked):
    """Lay out the Lean checker's constructor output; the kernel checks acceptance."""
    module = next(m for m in bundle["modules"]
                  if m["provenance"]["name"] == "shared::common::utils::Imperative")
    ds = [d for g in module["groups"]
          for d in (g["args"][0] if g["tag"] == "recursive" else g["args"])]
    bodies = checked["bodies"]
    if (checked["expression_typing"] != "accepted" or len(bodies) != 2
            or [b["name"] for b in bodies] != [d["name"]["origin"] for d in ds]
            or bodies[0]["scheme"] != bodies[1]["scheme"]
            or any(b["context"] != [ds[0]["name"]["origin"]] for b in bodies)
            or bodies[0]["recursive_group"] != [ds[0]["name"]["origin"]]
            or bodies[1]["recursive_group"]):
        raise ValueError("Imperative checked interface changed; update its consumer")
    source = '''/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ImperativeSource
public import PolyFunCryptol.Translation.ModuleElaboration
public import PolyFunCryptol.Model.PolyExamples

/-!
# Checked bodies of the complete Imperative module

Generated by the checked polynomial renderer from the retained module.
The acceptance equation in `Imperative.lean` checks these candidates against
whole-module elaboration; consumers can use these explicit bodies directly.
-/

public section

namespace Cryptol.Bridge.Imperative

open Polymorphic Translation

/-- The common polymorphic loop interface. -/
@[expose, reducible] def loopScheme : Scheme 0 0 :=
''' + wrap(bodies[0]["scheme"]) + '\n\n'
    for i, b in enumerate(bodies):
        source += f'/-- The complete retained body of `{b["name"]}`. -/\n'
        source += f'@[expose] def body{i} : Term Scope.empty [loopScheme] loopScheme :=\n'
        source += wrap(b["term"]) + '\n\n'
    source += '''/-- The candidate checked module with explicit, shared finite bodies. -/
@[expose, reducible] def imported : ElaboratedModule where
  source := ImperativeSource.source
  scope := Scope.empty
  parameters := []
  bindings :=
''' + wrap('[' + ', '.join('(' + name(d['name']) + ', loopScheme)' for d in reversed(ds)) + ']')
    source += '\n  code :=\n' + wrap(
        '.recursive [(' + name(ds[0]['name']) + ', loopScheme)] '
        '(Fin.cases body0 (fun i => nomatch i)) '
        '(.nonrecursive ' + name(ds[1]['name']) + ' loopScheme body1 (.nil _))')
    source += '''

end Cryptol.Bridge.Imperative
'''
    return source.encode()
