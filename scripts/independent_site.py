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
    '<a href="independent-review/">Interactive explorer</a> · ' \
    '<a href="paper/spectral-floor.pdf">Main paper (PDF)</a> · ' \
    '<a href="paper/independent-research-note.pdf">Independent verification (PDF)</a> · ' \
    '<a href="https://github.com/0thernes/hoggar-bound-lab">Code and proofs</a></nav>'
(DEST/'index.html').write_text(main_page.replace('<body>','<body>'+navigation,1),encoding='utf-8')
(DEST/'.nojekyll').write_text('')
(DEST/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')

class Links(HTMLParser):
    def handle_starttag(self,tag,attrs):
        for key,value in attrs:
            if key in ('href','src') and value and not value.startswith(('https:','http:','#')):
                target=(DEST/'independent-review'/value).resolve()
                if not target.exists():
                    raise RuntimeError(f'Broken local explorer link: {value}')
Links().feed((DEST/'independent-review/index.html').read_text(encoding='utf-8'))
if '--mirror-docs' in sys.argv:
    # Preserve the main author's docs/index.html, while making the companion
    # available to either a workflow deployment or branch-based Pages hosting.
    for name in FILES:
        dst=ROOT/'docs'/name
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(DEST/name,dst)
    shutil.copyfile(DEST/'artifact-sha256.json',ROOT/'docs'/'artifact-sha256.json')
print(f'Assembled {len(FILES)} files; all local explorer links resolve: {DEST}')
