"""Assemble only the selected public research artifacts for static hosting."""
from pathlib import Path
from html.parser import HTMLParser
import hashlib
import json
import shutil
import sys
from urllib.parse import unquote, urlsplit

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
    # Match the repository's LF checkout convention on every build platform.
    payload=src.read_bytes()
    if src.suffix not in {'.png','.pdf'}:
        payload=payload.replace(b'\r\n',b'\n')
    dst.write_bytes(payload)
    manifest[name]=hashlib.sha256(dst.read_bytes()).hexdigest()
main_page=(ROOT/'docs'/'research-index.html').read_text(encoding='utf-8')
if '\ufffd' in main_page:
    raise RuntimeError('Research landing page contains a Unicode replacement character')
(DEST/'index.html').write_bytes(main_page.encode('utf-8'))
manifest['index.html']=hashlib.sha256((DEST/'index.html').read_bytes()).hexdigest()
(DEST/'.nojekyll').write_text('')
(DEST/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')

class Links(HTMLParser):
    def __init__(self,page):
        super().__init__()
        self.page=page
        self.ids=set()
        self.references=[]
    def handle_starttag(self,tag,attrs):
        for key,value in attrs:
            if key=='id' and value:
                self.ids.add(value)
            if key in ('href','src') and value:
                parsed=urlsplit(value)
                if not parsed.scheme and not parsed.netloc:
                    target=(self.page.parent/unquote(parsed.path)).resolve() if parsed.path else self.page.resolve()
                    if target.is_dir():
                        target=target/'index.html'
                    if not target.is_file():
                        raise RuntimeError(f'Broken local link in {self.page.name}: {value}')
                    self.references.append((target,unquote(parsed.fragment),value))
pages=[DEST/'index.html']+[DEST/name for name in FILES if name.endswith('.html')]
parsed_pages={}
for page in pages:
    parser=Links(page)
    parser.feed(page.read_text(encoding='utf-8'))
    parser.close()
    parsed_pages[page.resolve()]=parser
for page,parser in parsed_pages.items():
    for target,fragment,value in parser.references:
        if fragment and target in parsed_pages and fragment not in parsed_pages[target].ids:
            raise RuntimeError(f'Broken local fragment in {page.name}: {value}')
if '--mirror-docs' in sys.argv:
    # Preserve the main author's docs/index.html. Workflow Pages uses the new
    # assembled index; a branch-based mirror exposes docs/research-index.html.
    for name in FILES:
        dst=ROOT/'docs'/name
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(DEST/name,dst)
    mirror_manifest={name:sha for name,sha in manifest.items() if name!='index.html'}
    mirror_manifest['research-index.html']=hashlib.sha256((ROOT/'docs'/'research-index.html').read_bytes()).hexdigest()
    (ROOT/'docs'/'artifact-sha256.json').write_text(json.dumps(mirror_manifest,indent=2)+'\n',encoding='utf-8')
print(f'Assembled {len(FILES)+1} files; all local links and HTML fragments resolve across {len(pages)} pages: {DEST}')
