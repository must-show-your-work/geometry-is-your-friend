import re
from pathlib import Path

COMMENT_RE = re.compile(r'--[^\n]*', re.MULTILINE)
BLOCK_COMMENT_RE = re.compile(r'/-.*?-/', re.DOTALL)
DOCSTRING_RE = re.compile(r'/--\s*(.*?)\s*-/', re.DOTALL)

DECL_RE = re.compile(
    r'\b(theorem|lemma|def|proposition|abbrev|axiom)\s+([\w.\']+)'
)

REF_RE = re.compile(r'[\w.\']+')

TEMPLATES = {
    'theorem':     ('theorem',     'thm'),
    'lemma':       ('lemma',       'lem'),
    'def':         ('definition',  'def'),
    'proposition': ('proposition', 'prop'),
    'abbrev':      ('definition',  'def'),
    'axiom':       ('axiom',       'ax'),
}

COMMENT_RE = re.compile(r'--[^\n]*', re.MULTILINE)
BLOCK_COMMENT_RE = re.compile(r'/-.*?-/', re.DOTALL)
DOCSTRING_RE = re.compile(r'/--\s*(.*?)\s*-/', re.DOTALL)

def strip_comments(src: str) -> str:
    src = BLOCK_COMMENT_RE.sub('', src)
    src = COMMENT_RE.sub('', src)
    return src

def strip_line_comments(src: str) -> str:
    """Only strip -- comments, leave block comments alone."""
    return COMMENT_RE.sub('', src)

def collect_all_names(root: Path) -> dict[str, str]:
    """Returns mapping of every possible reference form -> canonical name"""
    canonical = {}
    for lean_file in root.rglob('*.lean'):
        if not is_project_file(lean_file, root):
            continue
        src = strip_line_comments(lean_file.read_text())
        for m in DECL_RE.finditer(src):
            name = m.group(2)
            for suffix in all_suffixes(name):
                if suffix not in canonical:
                    canonical[suffix] = name
    return canonical

def extract_decls(path: Path, known_names: dict[str, str]):
    raw_src = path.read_text()
    src = strip_line_comments(raw_src)

    raw_matches = list(DECL_RE.finditer(raw_src))
    stripped_matches = list(DECL_RE.finditer(src))

    for i, (raw_m, m) in enumerate(zip(raw_matches, stripped_matches)):
        kind, name = m.group(1), m.group(2)
        start = m.end()
        end = stripped_matches[i+1].start() if i+1 < len(stripped_matches) else len(src)
        body = src[start:end]

        statement = extract_statement(src, m, end)
        docstring = extract_docstring(raw_src, raw_m.start())

        deps = list(dict.fromkeys(
            known_names[t] for t in REF_RE.findall(body)
            if t in known_names and known_names[t] != name
        ))

        yield kind, name, statement, docstring, body.strip(), deps

def is_project_file(path: Path, root: Path) -> bool:
    parts = path.relative_to(root).parts
    return parts[0] == 'Geometry' and 'lake-packages' not in parts

def all_suffixes(name: str) -> list[str]:
    """For 'Geometry.Ch2.Prop.P2' return all suffixes:
       ['Geometry.Ch2.Prop.P2', 'Ch2.Prop.P2', 'Prop.P2', 'P2']"""
    parts = name.split('.')
    return ['.'.join(parts[i:]) for i in range(len(parts))]

def extract_statement(src: str, decl_match, next_start: int) -> str:
    after_name = src[decl_match.end():next_start]
    assign = re.search(r':=\s*by\b|:=', after_name)
    if not assign:
        return ''
    sig = after_name[:assign.start()]
    sig = sig.strip().lstrip(':').strip()
    return sig

def extract_docstring(raw_src: str, decl_start: int) -> str:
    preceding = raw_src[max(0, decl_start-500):decl_start]
    # Find all docstrings in the preceding text, take the last one
    matches = list(DOCSTRING_RE.finditer(preceding))
    if not matches:
        return ''
    return matches[-1].group(1).strip()

def to_tex(kind, name, statement, docstring, deps, name_to_prefix):
    env, _ = TEMPLATES.get(kind, ('lemma', 'lem'))
    dep_str = ''
    if deps:
        dep_str = f'\n  \\uses{{{", ".join(deps)}}}'
    doc_str = f'\n  {docstring}' if docstring else '\n  % TODO: fill in statement'
    # Include the short name (last component) with the statement for readability
    short_name = name.split('.')[-1]
    full_stmt = f'{short_name} {statement}'.strip() if statement else ''
    stmt_str = f'\n\\begin{{verbatim}}{full_stmt}\\end{{verbatim}}' if full_stmt else ''
    return (
        f'\\begin{{{env}}}\n'
        f'  \\label{{{name}}}{dep_str}\n'
        f'  \\lean{{{name}}}\n'
        f'  \\leanok'
        f'{doc_str}'
        f'{stmt_str}\n'
        f'\\end{{{env}}}\n'
    )

def process_repo(root: Path, out_tex: Path):
    known_names = collect_all_names(root)
    print(f'Found {len(known_names)} name forms mapping to {len(set(known_names.values()))} canonical names')

    all_decls = []
    for lean_file in sorted(root.rglob('*.lean')):
        if not is_project_file(lean_file, root):
            continue
        for kind, name, statement, docstring, body, deps in extract_decls(lean_file, known_names):
            all_decls.append((lean_file, kind, name, statement, docstring, body, deps))

    name_to_prefix = {
        name: TEMPLATES.get(kind, ('lemma', 'lem'))[1]
        for _, kind, name, _, _, _, _ in all_decls
    }

    blocks = []
    current_file = None
    for lean_file, kind, name, statement, docstring, body, deps in all_decls:
        if lean_file != current_file:
            current_file = lean_file
            blocks.append(f'% === {lean_file.relative_to(root)} ===\n')
        valid_deps = [d for d in deps if d in name_to_prefix and d != name]
        blocks.append(to_tex(kind, name, statement, docstring, valid_deps, name_to_prefix))

    out_tex.write_text('\n'.join(blocks))
    print(f'Wrote {len(blocks)} entries to {out_tex}')

if __name__ == '__main__':
    import sys
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('.')
    out  = Path(sys.argv[2]) if len(sys.argv) > 2 else Path('blueprint/src/generated.tex')
    out.parent.mkdir(parents=True, exist_ok=True)
    process_repo(root, out)
