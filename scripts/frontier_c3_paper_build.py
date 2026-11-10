"""Typeset the C3 research preprint with the existing pinned Pandoc/Tectonic toolchain."""
from pathlib import Path
import argparse
import hashlib
import html
import json
import shutil
import subprocess
import tempfile
from independent_paper_build import PREAMBLE

ROOT=Path(__file__).resolve().parents[1]
STEM='c3-spectral-counterexample'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pandoc',default=shutil.which('pandoc'))
    parser.add_argument('--tectonic',default=shutil.which('tectonic'))
    args=parser.parse_args()
    if not args.pandoc or not args.tectonic:parser.error('Supply --pandoc and --tectonic executable paths')
    source=ROOT/'paper'/(STEM+'.md')
    markdown=source.read_text(encoding='utf-8')
    body='## Abstract'+markdown.split('## Abstract',1)[1]
    fragment=subprocess.run([args.pandoc,'--from=markdown+tex_math_dollars+tex_math_single_backslash',
                             '--to=latex','--wrap=none','--no-highlight','--shift-heading-level-by=-1'],input=body,
                            text=True,encoding='utf-8',capture_output=True,check=True).stdout
    fragment=fragment.replace(r'\def\LTcaptype{none}',r'\def\LTcaptype{table}')
    fragment=fragment.replace('c3-figures/spectra.png','c3-figures/spectra.pdf')
    fragment=fragment.replace(r'\begin{figure}',r'\begin{figure}[H]')
    fragment=fragment.replace('Expanding the cubes in',r'\Needspace{10\baselineskip}'+'\nExpanding the cubes in')
    fragment=fragment.replace(r'\begin{verbatim}',r'\Needspace{9\baselineskip}\begin{samepage}\begin{verbatim}')
    fragment=fragment.replace(r'\end{verbatim}',r'\end{verbatim}\end{samepage}')
    preamble=PREAMBLE.replace('A verified spectral bound for Pauli contextuality: independent validation and critical synthesis',
                             'Cospectral Pauli carriers with different completion spectra: an exact four-qubit C3 certificate')
    preamble=preamble.replace('Independent verification companion; research preprint, not peer reviewed',
                              'Exact four-qubit C3 certificate; research preprint, not peer reviewed')
    preamble=preamble.replace('Independent validation}', 'Four-qubit C3 certificate}')
    preamble=preamble.replace('INDEPENDENT VERIFICATION COMPANION','EXACT COUNTEREXAMPLE AND REPRODUCIBILITY STUDY')
    preamble=preamble.replace(r'A verified spectral bound\\for Pauli contextuality',r'Cospectral Pauli carriers\\with different completion spectra')
    preamble=preamble.replace('Independent validation and critical synthesis','An exact four-qubit C3 certificate')
    preamble=preamble.replace('pdfauthor={Hoggar Bound Lab; AI-assisted research artifact}',
                              'pdfauthor={Alexander S. Donahue; 0thernes LLC}')
    preamble=preamble.replace('Hoggar Bound Lab; AI-assisted research artifact',
                              r'Alexander S. Donahue · 0thernes LLC\\{\small\color{Muted}Hoggar Bound Lab · \href{mailto:0_0@0thernes.art}{0\_0@0thernes.art}}')
    tex=preamble+fragment+'\n\\end{document}\n'
    texpath=ROOT/'paper'/(STEM+'.tex');texpath.write_text(tex,encoding='utf-8')
    with tempfile.TemporaryDirectory(prefix='hoggar-c3-paper-') as tmp:
        stage=Path(tmp)/(STEM+'.tex');stage.write_text(tex,encoding='utf-8')
        shutil.copytree(ROOT/'paper/c3-figures',Path(tmp)/'c3-figures')
        result=subprocess.run([args.tectonic,'--untrusted','--keep-logs','--print',str(stage)],cwd=tmp,
                              text=True,encoding='utf-8',errors='replace',capture_output=True)
        (ROOT/'results/frontier-c3-paper-build.log').write_text(result.stdout+result.stderr,encoding='utf-8')
        if result.returncode:raise RuntimeError('Typesetting failed; see results/frontier-c3-paper-build.log')
        shutil.copyfile(Path(tmp)/(STEM+'.pdf'),ROOT/'paper'/(STEM+'.pdf'))
        shutil.copyfile(Path(tmp)/(STEM+'.log'),ROOT/'results/frontier-c3-paper-tex.log')
    title=markdown.splitlines()[0].removeprefix('# ')
    abstract=markdown.split('## Abstract',1)[1].split('\n## ',1)[0].strip()
    base='https://0thernes.github.io/hoggar-bound-lab/paper/'
    record='''<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title}</title>
<meta name="citation_title" content="{title}">
<meta name="citation_author" content="Donahue, Alexander S.">
<meta name="citation_publication_date" content="2026/11/09">
<meta name="citation_technical_report_institution" content="0thernes LLC">
<meta name="citation_pdf_url" content="{base}{stem}.pdf">
<link rel="canonical" href="{base}{stem}.html">
<style>body{{max-width:900px;margin:40px auto;padding:0 24px;font:17px/1.65 system-ui,sans-serif;color:#172f38;background:#f9fbfa}}h1{{font-size:31px;line-height:1.2;margin-bottom:20px}}.author{{font-size:21px;margin:0}}.meta{{color:#526971;font-size:14px}}a{{color:#116b61}}nav{{display:flex;flex-wrap:wrap;gap:18px}}section{{margin-top:27px}}footer{{border-top:1px solid #b8cbca;margin-top:35px;padding-top:18px;font-size:13px}}h2{{font-size:20px}}</style></head>
<body><article><h1 class="citation_title">{title}</h1>
<p class="citation_author author">Alexander S. Donahue</p>
<p class="meta">0thernes LLC · Hoggar Bound Lab · 9 November 2026<br>Research preprint; not peer reviewed. Correspondence: <a href="mailto:0_0@0thernes.art">0_0@0thernes.art</a></p>
<nav><a href="{stem}.pdf">Full paper (PDF)</a><a href="../c3-lab/">Run the exact demonstration</a><a href="https://github.com/0thernes/hoggar-bound-lab">Code and Lean proofs</a><a href="c3-citation.cff">Citation metadata</a></nav>
<section><h2>Abstract</h2><p>{abstract}</p></section>
<section><h2>Research and verification record</h2><p>The manuscript discloses substantive AI assistance in problem selection, discovery, formalization, computation and drafting. The repository contains exact witness assignments, independent integer checks, Lean sources, execution evidence and falsification controls. The original open case is stated in <a href="https://zenodo.org/records/23524332">Jonah’s section-square preprint, v0.5, Section 6</a>.</p></section>
<footer><a href="../">All Hoggar Bound Lab research artifacts</a> · Public availability is distinct from journal acceptance or indexing.</footer>
</article></body></html>'''.format(title=html.escape(title,quote=True),base=base,stem=STEM,abstract=html.escape(abstract))
    (ROOT/'paper'/(STEM+'.html')).write_text(record,encoding='utf-8')
    report={}
    for extension in ['md','tex','pdf','html']:
        data=(ROOT/'paper'/(STEM+'.'+extension)).read_bytes()
        report[extension+'_sha256']=hashlib.sha256(data).hexdigest()
        if extension!='pdf':report[extension+'_lf_sha256']=hashlib.sha256(data.replace(b'\r\n',b'\n')).hexdigest()
    report['pandoc']=subprocess.check_output([args.pandoc,'--version'],text=True).splitlines()[0]
    report['tectonic']=subprocess.check_output([args.tectonic,'--version'],text=True).strip()
    report['purpose']='Research preprint; exact theorem and declared formal boundary, not a claim of peer review'
    (ROOT/'results/frontier-c3-paper-build.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
