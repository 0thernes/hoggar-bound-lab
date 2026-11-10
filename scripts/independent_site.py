"""Assemble only the selected public research artifacts for static hosting."""
from pathlib import Path
from html.parser import HTMLParser
import hashlib
import json
import shutil
import sys

ROOT=Path(__file__).resolve().parents[1]
DEST=ROOT/'build'/'independent-site'
FILES=[
    'c3-lab/index.html','c3-lab/style.css','c3-lab/model.js','c3-lab/app.js','c3-lab/README.md',
    'paper/c3-spectral-counterexample.pdf','paper/c3-spectral-counterexample.md','paper/c3-spectral-counterexample.tex',
    'paper/c3-spectral-counterexample.html','paper/c3-citation.cff',
    'paper/c3-figures/spectra.png','paper/c3-figures/spectra.pdf','paper/c3-figures/spectra.svg',
    'results/frontier-c3-n4-pair.json','results/frontier-c3-n4-verification.json',
    'results/frontier-c3-context-verification.json','results/frontier-c3-n4-similarity.json',
    'results/frontier-c3-integer-bounds.json','results/frontier-c3-eshkol.json',
    'results/frontier-prior-art.md','results/frontier-c3-paper-build.json',
    'results/frontier-c3-lean-audit.md','results/frontier-c3-lean-axioms.log',
    'results/frontier-c3-lean-source-sha256.json','results/frontier-c3-certificate-audit.json',
    'results/frontier-c3-lean-certificate.log','results/frontier-c3-lean-certificate-process.json',
    'results/frontier-c3-lean-geometry.log','results/frontier-c3-lean-theorem.log',
    'results/frontier-c3-lean-spectra.log','results/frontier-c3-spectra-check.json',
    'results/frontier-c3-axioms.json','results/frontier-c3-paper-review.md',
    'results/frontier-c3-source-bundle-xelatex.json',
    'results/stability-lean-build.log','results/stability-lean-axioms.log','results/stability-axioms.json',
    'independent-review/index.html','independent-review/style.css','independent-review/explorer.js',
    'independent-review/model.js','independent-review/data.js','independent-review/README.md',
    'paper/independent-research-note.pdf','paper/independent-research-note.md','paper/independent-research-note.tex',
    'paper/independent-figures/spectral-bounds.pdf','paper/independent-figures/spectral-bounds.png',
    'paper/independent-figures/spectral-bounds.svg','results/lean-audit.md',
    'results/lean-independent-verification.log','results/lean-source-sha256.json',
    'results/independent_validation.json','results/stack-independent-audit.md','results/stack_audit.json',
    'results/literature-audit.md','results/independent-ci-audit.md',
    'results/independent-paper-build.json','results/independent-paper-review.json','INDEPENDENT-REVIEW.md',
    'paper/spectral-floor.md','paper/spectral-floor.html','paper/spectral-floor.pdf',
]
FILES += [str(p.relative_to(ROOT)).replace('\\','/') for p in sorted((ROOT/'paper'/'figures').glob('*.png'))]
manifest={}
for name in FILES:
    src,dst=ROOT/name,DEST/name
    if not src.is_file() or src.is_symlink():
        raise RuntimeError(f'Expected ordinary release file: {name}')
    dst.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(src,dst)
    manifest[name]=hashlib.sha256(dst.read_bytes()).hexdigest()
main_page=(ROOT/'docs'/'index.html').read_text(encoding='utf-8')
navigation='<nav style="max-width:46rem;margin:1rem auto;padding:0 16px;font:14px system-ui">' \
    '<a href="c3-lab/">New: four-qubit C3 certificate</a> · ' \
    '<a href="paper/c3-spectral-counterexample.html">C3 research paper</a> · ' \
    '<a href="independent-review/">Interactive explorer</a> · ' \
    '<a href="paper/spectral-floor.pdf">Main paper (PDF)</a> · ' \
    '<a href="paper/independent-research-note.pdf">Independent verification (PDF)</a> · ' \
    '<a href="https://github.com/0thernes/hoggar-bound-lab">Code and proofs</a></nav>'
(DEST/'index.html').write_text(main_page.replace('<body>','<body>'+navigation,1),encoding='utf-8')
(DEST/'.nojekyll').write_text('')
(DEST/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')

class Links(HTMLParser):
    def __init__(self,base):
        super().__init__()
        self.base=base
    def handle_starttag(self,tag,attrs):
        for key,value in attrs:
            if key in ('href','src') and value and not value.startswith(('https:','http:','mailto:','data:','#')):
                target=(self.base/value).resolve()
                if not target.exists():
                    raise RuntimeError(f'Broken local explorer link: {value}')
for directory in ('independent-review','c3-lab'):
    Links(DEST/directory).feed((DEST/directory/'index.html').read_text(encoding='utf-8'))
Links(DEST/'paper').feed((DEST/'paper/c3-spectral-counterexample.html').read_text(encoding='utf-8'))
if '--mirror-docs' in sys.argv:
    # Preserve the main author's docs/index.html, while making the companion
    # available to either a workflow deployment or branch-based Pages hosting.
    for name in FILES:
        dst=ROOT/'docs'/name
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(DEST/name,dst)
    shutil.copyfile(DEST/'artifact-sha256.json',ROOT/'docs'/'artifact-sha256.json')
print(f'Assembled {len(FILES)} files; all local explorer links resolve: {DEST}')
