"""Verify the compiled unified manuscript and its retained proof provenance.

This checks artifact consistency and recorded successful CI evidence. It does not
replace a Lean build, human mathematical review, or a journal's review process.
"""
from pathlib import Path
from html.parser import HTMLParser
import hashlib
import json
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
VERSION = '1.3.0'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(name):
    return json.loads((ROOT / name).read_text(encoding='utf-8'))


class Metadata(HTMLParser):
    def __init__(self):
        super().__init__()
        self.values = {}

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'meta' and 'name' in attrs:
            self.values[attrs['name']] = attrs.get('content', '')


def main():
    build = read('results/unified-paper-build.json')
    metadata = read('publication/unified-metadata.json')
    source = (ROOT / 'paper/unified-contextuality.md').read_bytes()
    require(build['publication_version'] == metadata['version'] == VERSION, 'Version mismatch')
    require((ROOT / 'VERSION').read_text().strip() == VERSION, 'Repository version mismatch')
    require(0 < len(metadata['abstract_plain_text']) <= 1920, 'Plain abstract exceeds the arXiv limit of 1920 characters')
    require(digest(source.replace(b'\r\n', b'\n')) == build['source_lf_sha256'], 'Canonical manuscript changed since build')
    require(source.decode('utf-8').splitlines()[0] == '# ' + metadata['title'], 'Manuscript title mismatch')
    text = source.replace(b'\r\n', b'\n').decode('utf-8')
    found = re.search(r'\n## Abstract\n\n(.*?)\n\n## 1\. ', text, re.S)
    require(found is not None and found.group(1) == metadata['abstract'], 'Metadata abstract differs from the paper')
    plain = (ROOT / 'publication/unified-abstract.txt').read_text(encoding='utf-8').strip()
    require(plain == metadata['abstract_plain_text'], 'Plain-text abstract file differs from the metadata')
    for name, record in build['artifacts'].items():
        path = (ROOT / name).resolve()
        require(ROOT.resolve() in path.parents and path.is_file() and not path.is_symlink(), 'Unsafe or missing artifact: ' + name)
        require(digest(path.read_bytes()) == record['sha256'], 'Compiled artifact mismatch: ' + name)
    public_pdf = (ROOT / 'paper/unified-contextuality.pdf').read_bytes()
    require(public_pdf == (ROOT / 'publication/unified-contextuality/unified-contextuality.pdf').read_bytes(), 'Public/typeset PDFs differ')
    require(len(public_pdf) < 5_000_000, 'PDF exceeds Scholar recommended size')
    page = Metadata()
    page.feed((ROOT / 'paper/unified-contextuality.html').read_text(encoding='utf-8'))
    require(page.values['citation_title'] == metadata['title'], 'HTML citation title mismatch')
    require(page.values['citation_author'] == 'Donahue, Alexander S.', 'HTML citation author mismatch')
    require(page.values['citation_author_institution'] == '0thernes LLC', 'HTML affiliation mismatch')
    require(page.values['citation_author_orcid'] == metadata['author']['orcid'], 'HTML ORCID mismatch')
    require(page.values['citation_pdf_url'] == metadata['public_pdf'], 'HTML PDF URL mismatch')
    require(metadata['abstract'] and not metadata['doi'] and not metadata['journal_submission_identifier'], 'Invalid current publication metadata')
    with zipfile.ZipFile(ROOT / 'publication/unified-contextuality/arxiv-source.zip') as archive:
        require(archive.testzip() is None, 'Corrupt arXiv source archive')
        require(all(not name.startswith('/') and '..' not in Path(name).parts for name in archive.namelist()), 'Unsafe archive member')
    ci = read('results/full-ci-87-audit.json')
    require(ci['status'] == 'pass' and ci['workflow_conclusion'] == 'success', 'Full CI did not pass')
    require(ci['checked_commit'] == '87f08a0fb5007c8529abc13eabeec093027c0eba', 'Unexpected CI revision')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for group, count in [('c3', 42), ('scalar_stability', 6), ('baseline', 22)]:
        audit = ci['axiom_audits'][group]
        require(audit['declarations'] == count and len(audit['actual']) == count, 'Axiom report size mismatch: ' + group)
        require(all(set(axioms) <= allowed for axioms in audit['actual'].values()), 'Nonstandard axiom: ' + group)
    result = {'status': 'pass', 'version': VERSION, 'manuscript_lf_sha256': build['source_lf_sha256'],
              'public_pdf_sha256': digest(public_pdf), 'compiled_artifacts_checked': len(build['artifacts']),
              'scholarly_metadata_consistent': True, 'public_pdf_equals_typeset_pdf': True,
              'recorded_full_ci': ci['run_url'], 'proof_sources_unchanged': 'See publication-v' + VERSION + '-audit.json',
              'scope': 'Artifact consistency and recorded CI provenance; not a new Lean build or peer review.'}
    (ROOT / 'results/unified-publication-audit.json').write_bytes((json.dumps(result, indent=2) + '\n').encode('utf-8'))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
