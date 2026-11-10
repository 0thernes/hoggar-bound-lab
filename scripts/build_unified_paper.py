"""Build the unified manuscript without changing either historical paper.

python scripts/build_unified_paper.py --pandoc PATH --tectonic PATH
Add --journal-main-only to update the journal manuscript while preserving the
existing complete paper, supplement and source archive byte-for-byte.

The canonical source is paper/unified-contextuality.md. A standalone comment
`<!-- journal:supplement -->` immediately before an H2 selects only that section
for the journal supplement. References appear in both journal documents;
section labels are preserved, including intentional gaps in the main document.
All compilation happens under build/unified-contextuality before final files
are replaced. No submission, upload, or commit is performed.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import html
import json
import os
import re
import shutil
import subprocess
import tempfile
from urllib.parse import quote, unquote, urlsplit
import zipfile

from build_latex import PREAMBLE, fit_tables

ROOT = Path(__file__).resolve().parents[1]
STEM = 'unified-contextuality'
SOURCE = ROOT / 'paper' / (STEM + '.md')
PUBLICATION = ROOT / 'publication' / STEM
RELEASE = 'v1.2.0'
TITLE = 'Spectral bounds and their limits in Pauli contextuality: exact configurations and a four-qubit C3 certificate'
SITE = 'https://0thernes.github.io/hoggar-bound-lab/'
REPOSITORY = 'https://github.com/0thernes/hoggar-bound-lab'
READER = 'gfm+tex_math_gfm+tex_math_dollars'
MARKER = '<!-- journal:supplement -->'
JOURNAL_ACKNOWLEDGMENTS = '''## Acknowledgments

**AI disclosure statement.** Claude (Anthropic) and OpenAI Codex were used for
substantive research, software development, formalization and manuscript preparation
under the author's direction. Section 13 describes their roles and the verification
performed in detail. AI systems are disclosed as tools, not authors; no independent
human peer review or venue-specific final approval is claimed.
'''
MATHJAX_URL = 'https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-chtml-full.min.js'
MATHJAX_INTEGRITY = 'sha384-dCtf/9Xgzj8edI30iIEsxNfjUQ0zj2AXa3eUdgjsx8odUmpURZx5Z7aDZmV781et'
CSS = '''
:root{color-scheme:light;--ink:#183239;--muted:#50666c;--rule:#cbd7d6;--accent:#126c61}
*{box-sizing:border-box}html{-webkit-text-size-adjust:100%;scroll-behavior:smooth}
body{margin:0;background:#fafbf8;color:var(--ink);font:17px/1.65 Georgia,serif}
main{max-width:55rem;margin:auto;padding:2.5rem 1.25rem 4rem;overflow-wrap:break-word}
h1{font-size:2.1rem;line-height:1.2;letter-spacing:-.025em;margin:1rem 0}
h2{font-size:1.45rem;line-height:1.3;margin-top:2.5rem;padding-top:1rem;border-top:1px solid var(--rule)}
h3{font-size:1.15rem;line-height:1.4;margin-top:1.8rem}p{margin:.8rem 0}
a{color:var(--accent);text-underline-offset:3px}a:focus-visible{outline:3px solid #b66b00;outline-offset:4px}
nav,.edition{font:14px/1.5 system-ui,sans-serif;color:var(--muted)}nav{display:flex;flex-wrap:wrap;gap:.6rem 1.2rem}
.contents{margin:1.5rem 0;padding:.8rem 1rem;border:1px solid var(--rule);font:15px/1.65 system-ui,sans-serif}.contents summary{cursor:pointer;font-weight:600}.contents ul{padding-left:1.3rem}
blockquote{border-left:3px solid var(--accent);padding:.6rem 1rem;margin:1.2rem 0;background:#eff4ef}
code{font: .85em/1.5 ui-monospace,Consolas,monospace;background:#edf1ed;padding:.1em .2em}
pre{overflow:auto;background:#edf1ed;padding:1rem;white-space:pre}pre code{padding:0}
img{display:block;max-width:100%;height:auto;margin:1.2rem auto;background:white}
table{display:block;max-width:100%;overflow-x:auto;border-collapse:collapse;font-size:.88rem;line-height:1.45}
th,td{padding:.45rem .6rem;border-bottom:1px solid var(--rule);text-align:left;vertical-align:top}
th{border-bottom:2px solid var(--ink)}mjx-container[display="true"]{overflow-x:auto;overflow-y:hidden;padding:.2rem 0}
.math.display{display:block;max-width:100%;overflow-x:auto;overflow-y:hidden}
main .math mjx-assistive-mml{width:1px!important;height:1px!important;min-width:0!important}
footer{margin-top:3rem;padding-top:1rem;border-top:1px solid var(--rule);font:14px/1.5 system-ui,sans-serif}
@media(max-width:600px){.math.inline{display:inline-block;max-width:100%;overflow-x:auto;overflow-y:hidden;vertical-align:middle}}
@media(max-width:500px){main{padding:1.4rem 1rem 3rem}h1{font-size:1.65rem}body{font-size:16px}}
@media print{body{background:white;color:black;font-size:10.5pt}main{max-width:none;padding:0}nav{display:none}h2,h3{break-after:avoid}img,blockquote,pre{break-inside:avoid}}
'''


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def plain(value):
    if isinstance(value, list):
        return ''.join(plain(item) for item in value)
    if not isinstance(value, dict):
        return ''
    kind, content = value.get('t'), value.get('c')
    if kind == 'Str':
        return content
    if kind in ('Space', 'SoftBreak', 'LineBreak'):
        return ' '
    if kind in ('Math', 'Code'):
        return content[1]
    return plain(content)


def normalize_math(source):
    """GFM handles its own math; adapt standalone TeX displays outside fences."""
    out, fence, display, count = [], None, False, 0
    for line in source.splitlines():
        token = re.match(r'^\s*(`{3,}|~{3,})', line)
        if token and not display:
            found = token[1]
            if fence is None:
                fence = found
            elif found[0] == fence[0] and len(found) >= len(fence):
                fence = None
            out.append(line)
            continue
        if fence is None and line.strip() in (r'\[', r'\]'):
            opening = line.strip() == r'\['
            require(opening != display, 'Unmatched standalone TeX display delimiter')
            display = opening
            count += int(opening)
            out.append('$$')
        else:
            out.append(line)
    require(not display, 'Unclosed standalone TeX display')
    return '\n'.join(out) + '\n', count


def run_pandoc(executable, source, target, *extra, reader=READER):
    run = subprocess.run([executable, '--from=' + reader, '--to=' + target,
                          '--wrap=preserve', *extra], input=source, capture_output=True,
                         text=True, encoding='utf-8', check=True)
    return run.stdout


def section_groups(blocks):
    sections, pending = [], False
    for block in blocks:
        if block.get('t') == 'RawBlock' and block['c'][1].strip() == MARKER:
            require(not pending, 'Duplicate supplement marker')
            pending = True
            continue
        if block.get('t') == 'Header' and block['c'][0] == 2:
            heading = plain(block['c'][2])
            sections.append({'heading': heading, 'supplement': pending,
                             'references': heading == 'References', 'blocks': [block]})
            pending = False
        else:
            require(not pending, 'Supplement marker must immediately precede an H2')
            require(sections, 'Body must begin with an H2')
            sections[-1]['blocks'].append(block)
    require(not pending, 'Dangling supplement marker')
    require(sum(s['references'] for s in sections) == 1, 'Expected one References section')
    require(any(s['supplement'] for s in sections), 'No journal supplement sections selected')
    require(not any(s['references'] and s['supplement'] for s in sections), 'References must be unmarked')
    return sections


def walk(node, transform):
    if isinstance(node, list):
        return [walk(value, transform) for value in node]
    if isinstance(node, dict):
        transformed = transform(node)
        return {key: walk(value, transform) for key, value in transformed.items()}
    return node


def publish_artifacts(artifacts):
    for name, payload in artifacts.items():
        destination = ROOT / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.resolve().relative_to(ROOT.resolve())
        require(not destination.is_symlink(), 'Refusing symlink output: ' + name)
        temporary = destination.with_name(destination.name + '.tmp')
        require(not temporary.exists(), 'Temporary output already exists: ' + str(temporary))
        temporary.write_bytes(payload)
        os.replace(temporary, destination)
        require(destination.read_bytes() == payload, 'Published file differs from staged bytes: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pandoc', default=shutil.which('pandoc'))
    parser.add_argument('--tectonic', default=shutil.which('tectonic'))
    parser.add_argument('--journal-main-only', action='store_true')
    args = parser.parse_args()
    require(args.pandoc and args.tectonic, 'Supply both --pandoc and --tectonic')
    args.pandoc = shutil.which(args.pandoc) or args.pandoc
    args.tectonic = shutil.which(args.tectonic) or args.tectonic
    source_bytes = SOURCE.read_bytes()
    source = source_bytes.decode('utf-8-sig').replace('\r\n', '\n')
    require('\ufffd' not in source, 'Source contains a replacement character')
    require(not re.search(r'(?m)^(<<<<<<< |>>>>>>> )', source), 'Source contains merge conflict markers')
    normalized, displays = normalize_math(source)
    abstract_marker = '\n## Abstract\n'
    require(normalized.count(abstract_marker) == 1, 'Expected exactly one Abstract heading')
    front, remainder = normalized.split(abstract_marker)
    first_heading = re.search(r'(?m)^## ', remainder)
    require(first_heading is not None, 'Missing manuscript sections')
    abstract_md, body_md = remainder[:first_heading.start()].strip(), remainder[first_heading.start():]
    front_parts = re.split(r'\n\s*\n', front.strip(), maxsplit=3)
    require(len(front_parts) >= 3 and front_parts[0] == '# ' + TITLE, 'Unexpected title or front matter')
    subtitle, byline = front_parts[1], front_parts[2].replace('<br>', '')
    note = front_parts[3] if len(front_parts) > 3 else ''
    date = re.search(r'version (\d+\.\d+\.\d+), (\d+) (\w+) (\d{4})', byline)
    require(date is not None and 'v' + date[1] == RELEASE, 'Expected the unified v1.2.0 byline')
    months = 'January February March April May June July August September October November December'.split()
    citation_date = f'{date[4]}/{months.index(date[3])+1:02d}/{int(date[2]):02d}'
    ast = json.loads(run_pandoc(args.pandoc, body_md, 'json'))
    sections = section_groups(ast['blocks'])
    mapping = [{'heading': s['heading'], 'journal': 'both' if s['references'] else
                ('supplement' if s['supplement'] else 'main')} for s in sections]
    snapshot = {SOURCE: source_bytes, Path(__file__): Path(__file__).read_bytes(),
                ROOT / 'scripts/build_latex.py': (ROOT / 'scripts/build_latex.py').read_bytes()}
    images = {}

    def transform_links(node, latex=False):
        result = copy.deepcopy(node)
        if latex and result.get('t') == 'Code':
            code = result['c'][1]
            if len(code) >= 24 and re.fullmatch(r'[A-Za-z0-9_./:-]+', code):
                return {'t': 'RawInline', 'c': ['latex', r'\nolinkurl{' + code + '}']}
        if result.get('t') not in ('Image', 'Link'):
            return result
        address = result['c'][2][0]
        parsed = urlsplit(address)
        if result['t'] == 'Image':
            require(not parsed.scheme and not parsed.netloc and not parsed.query and not parsed.fragment,
                    'Figures must be local files: ' + address)
            relative = Path(unquote(parsed.path))
            require(relative.parts and relative.parts[0] in ('figures', 'c3-figures') and '..' not in relative.parts,
                    'Unexpected figure path: ' + address)
            if latex and relative.as_posix() == 'c3-figures/spectra.png':
                relative = Path('c3-figures/spectra.pdf')
            path = ROOT / 'paper' / relative
            require(path.is_file() and not path.is_symlink(), 'Missing ordinary figure: ' + str(relative))
            path.resolve().relative_to((ROOT / 'paper').resolve())
            payload = path.read_bytes()
            snapshot[path] = payload
            images[relative.as_posix()] = payload
            result['c'][2][0] = relative.as_posix()
        elif not parsed.scheme and not parsed.netloc and parsed.path:
            path = (ROOT / 'paper' / unquote(parsed.path)).resolve()
            relative = path.relative_to(ROOT.resolve()).as_posix()
            require(path.exists(), 'Missing repository link target: ' + address)
            kind = 'tree' if path.is_dir() else 'blob'
            result['c'][2][0] = REPOSITORY + '/' + kind + '/' + RELEASE + '/' + quote(relative, safe='/')
            if parsed.fragment:
                result['c'][2][0] += '#' + parsed.fragment
        return result

    def document(blocks):
        return dict(ast, blocks=blocks)

    def render(blocks, target):
        changed = walk(document(blocks), lambda n: transform_links(n, latex=target == 'latex'))
        options = ['--mathjax'] if target == 'html5' else ['--no-highlight']
        output = run_pandoc(args.pandoc, json.dumps(changed), target, *options, reader='json')
        return fit_tables(output) if target == 'latex' else output

    def parse(md):
        return json.loads(run_pandoc(args.pandoc, md, 'json'))['blocks']

    def tex(md):
        return render(parse(md), 'latex').strip()

    all_blocks = [block for section in sections for block in section['blocks']]
    main_blocks = [block for section in sections if not section['supplement'] for block in section['blocks']]
    references_index = next(i for i, block in enumerate(main_blocks)
                            if block.get('t') == 'Header' and block['c'][0] == 2
                            and plain(block['c'][2]) == 'References')
    main_blocks[references_index:references_index] = parse(JOURNAL_ACKNOWLEDGMENTS)
    supp_blocks = [block for section in sections if section['supplement'] or section['references'] for block in section['blocks']]
    supp_labels = ', '.join(s['heading'] for s in sections if s['supplement'])
    journal_note = ('This journal-format document is derived from the complete paper, version 1.2.0. '
                    'Original section numbers and cross-references are retained; gaps are intentional. '
                    'The supplement contains: ' + supp_labels + '. References are reproduced in both journal documents.')
    bylines = byline.splitlines()
    who, _, email = bylines[0].partition('Correspondence:')
    who, _, orcid = who.partition('ORCID:')
    author, _, affiliation = who.rstrip('. ').partition(',')
    require(author.strip() == 'Alexander S. Donahue' and email.strip(), 'Unexpected author or missing correspondence')
    author_tex = tex(author) + r'\\' + tex(affiliation.rstrip('. '))
    if orcid.strip():
        author_tex += r'\\ORCID ' + tex(orcid.rstrip('. '))
    author_tex += r'\\\texttt{' + email.strip().replace('_', r'\_') + '}'
    preamble = PREAMBLE.replace('% Generated by scripts/build_latex.py from paper/spectral-floor.md.',
                                '% Generated by scripts/build_unified_paper.py from paper/unified-contextuality.md.')
    preamble += '\n\\hypersetup{pdftitle={' + tex(TITLE) + '},pdfauthor={Alexander S. Donahue; 0thernes LLC}}\n'

    def latex_document(blocks, kind):
        title = tex(TITLE)
        if kind == 'supplement':
            title = r'Supplementary material\\[0.5em]\large ' + title
        body = [preamble, r'\title{' + title + '}', r'\author{' + author_tex + '}', r'\date{}',
                r'\begin{document}', r'\maketitle', tex('\n'.join(bylines[1:]))]
        if kind != 'supplement':
            body += [tex(subtitle), tex(note), r'\begin{abstract}', tex(abstract_md), r'\end{abstract}']
        if kind != 'full':
            body += [tex(journal_note)]
        body += [render(blocks, 'latex'), r'\end{document}', '']
        return '\n\n'.join(body)

    full_tex = latex_document(all_blocks, 'full')
    main_tex = latex_document(main_blocks, 'main')
    supp_tex = latex_document(supp_blocks, 'supplement')
    front_blocks = parse(front + abstract_marker + abstract_md)
    html_blocks = front_blocks + all_blocks
    contents = '<details class="contents"><summary>Contents</summary><ul>' + ''.join(
        '<li><a href="#' + html.escape(s['blocks'][0]['c'][1][0], quote=True) + '">' +
        html.escape(s['heading']) + '</a></li>' for s in sections) + '</ul></details>'
    html_body = render(front_blocks, 'html5') + contents + render(all_blocks, 'html5')
    math_counts = {'inline': 0, 'display': 0}

    def count_math(node):
        if node.get('t') == 'Math':
            math_counts['display' if node['c'][0]['t'] == 'DisplayMath' else 'inline'] += 1
        return node

    walk(html_blocks, count_math)
    tags = {'citation_title': TITLE, 'citation_author': 'Donahue, Alexander S.',
            'citation_author_institution': '0thernes LLC', 'citation_author_orcid': 'https://orcid.org/0009-0006-8168-9648',
            'citation_publication_date': citation_date, 'citation_online_date': citation_date,
            'citation_technical_report_institution': '0thernes LLC',
            'citation_technical_report_number': 'Hoggar Bound Lab, version 1.2.0',
            'citation_pdf_url': SITE + 'paper/' + STEM + '.pdf',
            'citation_abstract_html_url': SITE + 'paper/' + STEM + '.html', 'citation_language': 'en'}
    metadata = '\n'.join('<meta name="' + key + '" content="' + html.escape(value, quote=True) + '">' for key, value in tags.items())
    mathjax = r'''<script>window.MathJax={tex:{inlineMath:[['\\(','\\)']],displayMath:[['\\[','\\]']]},options:{skipHtmlTags:['script','noscript','style','textarea','pre','code']},startup:{pageReady:()=>MathJax.startup.defaultPageReady().then(()=>{document.documentElement.setAttribute('data-math','ready')})}};</script>'''
    page = ('<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>' + html.escape(TITLE) + '</title>\n' + metadata + '\n'
            '<link rel="canonical" href="' + SITE + 'paper/' + STEM + '.html">'
            '<style>' + CSS + '</style>' + mathjax + '<script src="' + MATHJAX_URL + '" integrity="' + MATHJAX_INTEGRITY + '" crossorigin="anonymous"></script>'
            '</head><body><main><nav aria-label="Research links"><a href="../">Research index</a>'
            '<a href="' + STEM + '.pdf">Full paper PDF</a><a href="../c3-lab/">C3 demonstration</a>'
            '<a href="' + REPOSITORY + '/tree/' + RELEASE + '/lean">Lean proofs</a></nav>' + html_body +
            '<footer>Version 1.2.0. Research preprint; not peer reviewed. The journal manuscript and supplement are formats of this paper. '
            '<a href="' + REPOSITORY + '/blob/' + RELEASE + '/publication/PAPER-MAP.md">Publication map</a></footer></main></body></html>\n')
    require(MARKER not in page and '\ufffd' not in page, 'Unprocessed marker or invalid character in HTML')
    temp_root = ROOT / 'build' / STEM
    temp_root.mkdir(parents=True, exist_ok=True)
    temp_root.resolve().relative_to((ROOT / 'build').resolve())
    stage = Path(tempfile.mkdtemp(prefix='run-', dir=temp_root))
    print('Compiling staged documents in ' + str(stage), flush=True)
    staged_outputs = {}
    compile_records = {}

    def compile_one(relative, content):
        path = stage / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content.encode('utf-8'))
        for name, payload in images.items():
            image_path = path.parent / name
            image_path.parent.mkdir(parents=True, exist_ok=True)
            image_path.write_bytes(payload)
        run = subprocess.run([args.tectonic, '--untrusted', '--keep-logs', path.name], cwd=path.parent,
                             capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=600)
        log = run.stdout + run.stderr
        log_path = path.with_name(path.stem + '-tectonic.log')
        log_path.write_bytes(log.encode('utf-8'))
        require(run.returncode == 0, 'Tectonic failed; inspect ' + str(log_path))
        missing = sorted(set(re.findall(r'could not represent character "(.)"|Missing character: ([^\n]+)', log)))
        require(not missing, 'Missing glyphs; inspect ' + str(log_path))
        pdf = path.with_suffix('.pdf')
        require(pdf.is_file() and pdf.stat().st_size > 1000, 'No fresh PDF: ' + str(pdf))
        overfull = sorted({float(x) for x in re.findall(r'Overfull \\hbox \(([0-9.]+)pt too wide\)', log)})
        compile_records[relative] = {'returncode': run.returncode, 'missing_characters': missing, 'overfull_boxes_pt': overfull}
        for artifact in (path, pdf, log_path):
            staged_outputs[artifact.relative_to(stage).as_posix()] = artifact.read_bytes()
        for name in sorted(set(re.findall(r'includegraphics(?:\[[^\]]*\])?\{([^}]+)\}', content))):
            require(name in images, 'Unknown TeX image: ' + name)
            staged_outputs[(path.parent.relative_to(stage) / name).as_posix()] = images[name]
        print('Built ' + relative + ' (' + str(pdf.stat().st_size) + ' PDF bytes)', flush=True)

    if args.journal_main_only:
        record = json.loads((PUBLICATION / 'build-record.json').read_text(encoding='utf-8'))
        require(record['source_sha256'] == digest(source_bytes), 'Partial build requires the same canonical source')
        require((PUBLICATION / (STEM + '.tex')).read_bytes() == full_tex.encode('utf-8'),
                'Complete TeX changed; run a full build instead')
        require((ROOT / 'paper' / (STEM + '.html')).read_bytes() == page.encode('utf-8'),
                'Public HTML changed; run a full build instead')
        require((PUBLICATION / 'jphysa/supplementary.tex').read_bytes() == supp_tex.encode('utf-8'),
                'Supplement TeX changed; run a full build instead')
        preserved = {}
        for name, meta in record['artifacts'].items():
            payload = (ROOT / name).read_bytes()
            require(digest(payload) == meta['sha256'], 'Existing artifact differs from build record: ' + name)
            if name not in {'publication/' + STEM + '/jphysa/manuscript' + suffix
                            for suffix in ('.tex', '.pdf', '-tectonic.log')}:
                preserved[name] = payload
        for name, executable in [('pandoc', args.pandoc), ('tectonic', args.tectonic)]:
            require(digest(Path(executable).read_bytes()) == record['tools'][name]['sha256'],
                    'Partial build requires the recorded ' + name + ' binary')
        compile_one('jphysa/manuscript.tex', main_tex)
        for path, payload in snapshot.items():
            require(path.read_bytes() == payload, 'Input changed during build: ' + str(path))
        artifacts = {'publication/' + STEM + '/' + name: payload
                     for name, payload in staged_outputs.items() if name.startswith('jphysa/manuscript')}
        record.setdefault('preserved_full_build_builder_sha256', record['builder_sha256'])
        record['builder_sha256'] = digest(Path(__file__).read_bytes())
        record['latest_build_mode'] = 'journal-main-only'
        record['journal_generated_sections'] = [{'heading': 'Acknowledgments', 'journal': 'main',
                                                'origin': 'journal template; inserted before References',
                                                'markdown': JOURNAL_ACKNOWLEDGMENTS}]
        record['journal_main_revision'] = {'scope': 'Separate AI disclosure in Acknowledgments; detailed Section13 retained.',
                                           'preserved_artifacts_sha256': {name: digest(payload) for name, payload in preserved.items()}}
        record['compilation'].update(compile_records)
        for name, payload in artifacts.items():
            record['artifacts'][name] = {'sha256': digest(payload), 'bytes': len(payload)}
        record_bytes = (json.dumps(record, indent=2) + '\n').encode('utf-8')
        artifacts['publication/' + STEM + '/build-record.json'] = record_bytes
        artifacts['results/unified-paper-build.json'] = record_bytes
        publish_artifacts(artifacts)
        for name, payload in preserved.items():
            require((ROOT / name).read_bytes() == payload, 'Preserved artifact changed: ' + name)
        print(json.dumps({'status': 'built', 'mode': 'journal-main-only', 'artifacts': list(artifacts),
                          'preserved_artifact_count': len(preserved), 'compilation': compile_records}, indent=2))
        return

    compile_one(STEM + '.tex', full_tex)
    compile_one('jphysa/manuscript.tex', main_tex)
    compile_one('jphysa/supplementary.tex', supp_tex)
    readme = {'spec_version': 1, 'process': {'compiler': 'xelatex'},
              'sources': [{'filename': STEM + '.tex', 'usage': 'toplevel'}], 'texlive_version': 2025}
    archive_members = {'00README.json': (json.dumps(readme, indent=2) + '\n').encode(),
                       STEM + '.tex': full_tex.encode('utf-8')}
    for name in sorted(set(re.findall(r'includegraphics(?:\[[^\]]*\])?\{([^}]+)\}', full_tex))):
        archive_members[name] = images[name]
    zip_path = stage / 'arxiv-source.zip'
    with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as archive:
        for name, payload in sorted(archive_members.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 9, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, payload)
    with zipfile.ZipFile(zip_path) as archive:
        require(archive.testzip() is None, 'Source ZIP CRC check failed')
        require(set(archive.namelist()) == set(archive_members), 'Source ZIP member mismatch')
        require(all(archive.read(name) == payload for name, payload in archive_members.items()), 'Source ZIP byte mismatch')
        archive_check = stage / 'source-check'
        for name in archive.namelist():
            target = archive_check / name
            target.resolve().relative_to(archive_check.resolve())
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.read(name))
    archive_run = subprocess.run([args.tectonic, '--untrusted', '--keep-logs', STEM + '.tex'], cwd=archive_check,
                                 capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=600)
    archive_log = archive_run.stdout + archive_run.stderr
    (archive_check / 'archive-build.log').write_bytes(archive_log.encode('utf-8'))
    require(archive_run.returncode == 0, 'Fresh source ZIP rebuild failed; inspect ' + str(archive_check))
    archive_pdf = (archive_check / (STEM + '.pdf')).read_bytes()
    require(len(archive_pdf) > 1000, 'Fresh source ZIP did not produce a PDF')
    staged_outputs['arxiv-source.zip'] = zip_path.read_bytes()
    staged_outputs['arxiv-source-tectonic.log'] = archive_log.encode('utf-8')
    staged_outputs['journal-section-map.json'] = (json.dumps(mapping, indent=2) + '\n').encode()
    staged_outputs[STEM + '.html'] = page.encode('utf-8')
    # The complete HTML also needs the PNG version of the C3 vector figure.
    staged_outputs.update(images)
    artifacts = {('publication/' + STEM + '/' + name): payload for name, payload in staged_outputs.items()}
    artifacts['paper/' + STEM + '.pdf'] = staged_outputs[STEM + '.pdf']
    artifacts['paper/' + STEM + '.html'] = page.encode('utf-8')
    for path, payload in snapshot.items():
        require(path.read_bytes() == payload, 'Input changed during build: ' + str(path))
    tools = {}
    for name, executable in [('pandoc', args.pandoc), ('tectonic', args.tectonic)]:
        version = subprocess.check_output([executable, '--version'], text=True, encoding='utf-8').splitlines()[0]
        tools[name] = {'version': version, 'sha256': digest(Path(executable).read_bytes())}
    record = {'status': 'built', 'publication_version': '1.2.0', 'source': 'paper/' + STEM + '.md',
              'source_sha256': digest(source_bytes), 'source_lf_sha256': digest(source.encode()),
              'builder_sha256': digest(Path(__file__).read_bytes()),
              'table_helper_sha256': digest((ROOT / 'scripts/build_latex.py').read_bytes()),
              'tools': tools, 'reader': READER, 'normalized_standalone_displays': displays,
              'math_expression_counts': math_counts,
              'journal_section_map': mapping, 'compilation': compile_records,
              'latest_build_mode': 'full',
              'journal_generated_sections': [{'heading': 'Acknowledgments', 'journal': 'main',
                                               'origin': 'journal template; inserted before References',
                                               'markdown': JOURNAL_ACKNOWLEDGMENTS}],
              'mathjax': {'url': MATHJAX_URL, 'integrity': MATHJAX_INTEGRITY},
              'arxiv_members': sorted(archive_members),
              'arxiv_archive_rebuild': {'returncode': archive_run.returncode, 'pdf_bytes': len(archive_pdf),
                                        'pdf_sha256': digest(archive_pdf), 'engine': 'Tectonic / XeTeX',
                                        'scope': 'Fresh extraction compiled using the installed TeX package cache; no arXiv submission or service-side compilation.'},
              'figures': {name: {'sha256': digest(payload), 'bytes': len(payload)} for name, payload in sorted(images.items())},
              'artifacts': {name: {'sha256': digest(payload), 'bytes': len(payload)} for name, payload in sorted(artifacts.items())},
              'public_pdf_matches_typeset_pdf': artifacts['paper/' + STEM + '.pdf'] == staged_outputs[STEM + '.pdf'],
              'submission_status': 'Prepared locally; no arXiv, Zenodo or journal submission.',
              'validation_boundary': 'Compilation, source/archive consistency and input stability checked; rendered layout requires separate visual review.'}
    record_bytes = (json.dumps(record, indent=2) + '\n').encode('utf-8')
    artifacts['publication/' + STEM + '/build-record.json'] = record_bytes
    artifacts['results/unified-paper-build.json'] = record_bytes
    # Each destination is replaced atomically only after all three builds pass.
    publish_artifacts(artifacts)
    print(json.dumps({'status': 'built', 'artifacts': len(artifacts), 'source_sha256': record['source_sha256'],
                      'journal_section_map': mapping, 'compilation': compile_records}, indent=2))


if __name__ == '__main__':
    main()
