#!/usr/bin/env bash
# Enforce the import boundaries of optional language and verification backends.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  echo "Usage: scripts/check-interop-isolation.sh"
  exit 0
fi
python3 - <<'CHECK'
from pathlib import Path
import re

CORE = {"VCVio", "VCVioCslib", "LatticeCrypto", "LatticeCryptoTest", "HashSig",
        "HashSigTest", "Examples", "ToMathlib", "Extern", "VCVioWidgets", "VCVioTest"}
BASE = {"Init", "Std", "Lean", "Mathlib", "Batteries", "Cslib", "ToCslib", "PolyFun", "Qq", "Aesop"}

def imports(text):
    # Remove nested Lean block comments before inspecting every import modifier.
    depth = 0
    cleaned = []
    i = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            if depth == 0: cleaned.append(' ')
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n': cleaned.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            cleaned.append(text[i])
            i += 1
    cleaned = ''.join(cleaned)
    commands = {'public', 'meta', 'private', 'import', 'module', 'namespace', 'open',
                'section', 'end', 'def', 'theorem', 'lemma', 'abbrev', 'inductive',
                'structure', 'class', 'instance', 'variable', 'universe', 'set_option',
                'noncomputable', 'initialize', 'attribute', 'export'}
    identifier = re.compile(r"(?:[\w']+|«[^»]+»)(?:\.(?:[\w']+|«[^»]+»))*")
    for match in re.finditer(r'(?m)^[ \t]*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?',
                             cleaned):
        pos = match.end()
        while pos < len(cleaned):
            while pos < len(cleaned) and cleaned[pos].isspace(): pos += 1
            module = identifier.match(cleaned, pos)
            if not module or module[0] in commands: break
            yield cleaned.count('\n', 0, pos) + 1, module[0]
            pos = module.end()

violations = []
paths = set()
for root in CORE | {'Interop'}:
    paths.update(Path(root).rglob('*.lean'))
    if Path(root + '.lean').is_file(): paths.add(Path(root + '.lean'))
for path in sorted(paths):
    if path.name == 'lakefile.lean': continue
    owner = path.parts[0].removesuffix('.lean')
    for line, name in imports(path.read_text()):
        head = name.split('.')[0]
        allowed = True
        if owner in CORE:
            allowed = head not in {'Interop', 'Hax', 'Aeneas'}
        elif path.parts[:2] == ('Interop', 'Cryptol'):
            component = path.parts[2].removesuffix('.lean')
            if component == 'Consumer': component = 'Tests'
            layers = {'Model': {'Model'}, 'Translation': {'Model', 'Translation'},
                      'Bridge': {'Model', 'Translation', 'Bridge'},
                      'Tests': {'Model', 'Translation', 'Bridge', 'Tests'},
                      'Main': {'Model', 'Translation', 'Bridge'}}
            allowed = head in BASE
            if name.startswith('Interop.Cryptol.'):
                allowed = name.split('.')[2] in layers.get(component, set())
            if component in {'Bridge', 'Tests', 'Main'} and head in {'VCVio', 'ToMathlib', 'HashSig'}:
                allowed = True
        else:
            allowed = head not in (CORE - {'VCVio', 'ToMathlib'}) and not name.startswith('Interop.Cryptol')
        if not allowed:
            violations.append(f'{path}:{line}: forbidden import {name}')
if violations:
    raise SystemExit('Interop isolation failed:\n' + '\n'.join(violations))
print('Interop isolation: core, model, translation, bridge, and dormant backend boundaries OK')
CHECK
