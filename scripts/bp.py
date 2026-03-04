#!/usr/bin/env python3
"""
gen_bp.py - Generate Lean Blueprint LaTeX from decls.json
Usage: python scripts/gen_bp.py [repo_root] [output_tex]
"""

import json
import re
import subprocess
from dataclasses import dataclass, field
from itertools import groupby
from pathlib import Path


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

INFRA_TYPES = {
    'TacticM', 'MetaM', 'TermElabM', 'CommandElabM', 'CoreM',
    'MacroM', 'AttrM', 'TrailingParserDescr', 'ParserDescr',
    'Lean.Elab', 'Lean.Meta', 'Lean.Parser',
}

TEX_ENV = {
    'axiom':   'lemma',
    'theorem': 'theorem',
    'def':     'definition',
    'opaque':  'definition',
    'other':   'lemma',
}


@dataclass
class Decl:
    name: str
    kind: str
    doc: str
    type_str: str
    deps: list[str] = field(default_factory=list)

    @property
    def short_name(self) -> str:
        return self.name.split('.')[-1]

    @property
    def tex_env(self) -> str:
        return TEX_ENV.get(self.kind, 'lemma')

    def to_tex(self, name_to_decl: dict[str, 'Decl']) -> str:
        lines = []
        lines.append(f'\\begin{{{self.tex_env}}}')
        lines.append(f'  \\label{{{self.name}}}')

        valid_deps = [d for d in self.deps if d in name_to_decl and d != self.name]
        if valid_deps:
            lines.append(f'  \\uses{{{", ".join(valid_deps)}}}')

        lines.append(f'  \\lean{{{self.name}}}')
        lines.append(f'  \\leanok')

        if self.doc:
            lines.append(f'  {self.doc}')
        else:
            lines.append(f'  % TODO: fill in statement')

        if self.type_str:
            stmt = self.type_str.replace('\n', ' ').strip()
            lines.append(f'\\begin{{verbatim}}{self.short_name} : {stmt}\\end{{verbatim}}')

        lines.append(f'\\end{{{self.tex_env}}}')
        return '\n'.join(lines)


# ---------------------------------------------------------------------------
# Filtering
# ---------------------------------------------------------------------------

def is_user_decl(decl: Decl) -> bool:
    # Reject «»-escaped names (syntax/macro internals)
    if '«' in decl.name or '»' in decl.name:
        return False
    # Reject any name component that starts with underscore
    parts = decl.name.split('.')
    if any(p.startswith('_') for p in parts):
        return False
    # Reject infrastructure types
    if any(t in decl.type_str for t in INFRA_TYPES):
        return False
    return True


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------

def load_decls(decls_json: Path) -> list[Decl]:
    raw = json.loads(decls_json.read_text())
    decls = [Decl(
        name=d['name'],
        kind=d['kind'],
        doc=d.get('doc', ''),
        type_str=d.get('type', ''),
        deps=d.get('deps', []),
    ) for d in raw]
    before = len(decls)
    decls = [d for d in decls if is_user_decl(d)]
    print(f'Filtered {before - len(decls)} infra declarations, {len(decls)} remaining')
    return decls


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def module_key(decl: Decl) -> str:
    parts = decl.name.split('.')
    return '.'.join(parts[:-1]) if len(parts) > 1 else decl.name


def process(root: Path, out_tex: Path) -> None:
    decls_json = root / 'blueprint' / 'decls.json'

    if not decls_json.exists():
        print('blueprint/decls.json not found, running lake exe dumpdecls...')
        subprocess.run(['lake', 'exe', 'dumpdecls'], cwd=root, check=True)

    decls = load_decls(decls_json)
    print(f'Loaded {len(decls)} declarations after filtering')

    # Build lookup for dep validation — only keep deps that are user decls
    name_to_decl = {d.name: d for d in decls}


    # Filter each decl's deps to only known user decls
    for decl in decls:
        before = decl.deps
        decl.deps = [d for d in decl.deps if d in name_to_decl and d != decl.name]
        if decl.name == 'Geometry.Ch2.Prop.P2':
            print(f'P2 deps before: {before}')
            print(f'P2 deps after:  {decl.deps}')
            print(f'I1 in name_to_decl: {"Geometry.Theory.I1" in name_to_decl}')

    decls_sorted = sorted(decls, key=module_key)

    blocks: list[str] = []
    for module, group in groupby(decls_sorted, key=module_key):
        group_list = list(group)
        blocks.append(f'% === {module} ===\n')
        for decl in group_list:
            blocks.append(decl.to_tex(name_to_decl))
            blocks.append('')

    out_tex.write_text('\n'.join(blocks))
    print(f'Wrote {len(decls)} entries to {out_tex}')


if __name__ == '__main__':
    import sys
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('.')
    out  = Path(sys.argv[2]) if len(sys.argv) > 2 else root / 'blueprint' / 'src' / 'generated.tex'
    out.parent.mkdir(parents=True, exist_ok=True)
    process(root, out)
