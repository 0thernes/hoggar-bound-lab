"""Build a minimal, licensed C3 TeX source archive; never submit it anywhere.

Default profile: arXiv's supported XeLaTeX engine, using TeX Live font filenames.
The optional pdfLaTeX profile uses Latin Modern and conventional AMS mathematics.
Validation records the actual local engine; Tectonic is not claimed to be pdfLaTeX.
"""

from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "paper/c3-spectral-counterexample.tex"
MARKDOWN = ROOT / "paper/c3-spectral-counterexample.md"
FIGURE = ROOT / "paper/c3-figures/spectra.pdf"
POLICY_DATE = "2026-11-09"
POLICIES = {
    "processors_fonts": "https://info.arxiv.org/help/faq/texlive.html",
    "source_files": "https://info.arxiv.org/help/submit_tex.html",
    "filenames": "https://info.arxiv.org/help/submit/index.html",
    "ancillary": "https://info.arxiv.org/help/ancillary_files.html",
    "tex_live_fonts": "https://info.arxiv.org/help/faq/font-info-tl2025.html",
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def normalized(data):
    return data.replace(b"\r\n", b"\n")


def portable_tex(source, profile):
    if source.count(r"\begin{document}") != 1:
        raise ValueError("Expected exactly one document in generated source")
    preamble, body = source.split(r"\begin{document}", 1)
    original_body = body
    if body.count("c3-figures/spectra.pdf") != 1:
        raise ValueError("Expected precisely the known spectrum figure")
    body = body.replace("c3-figures/spectra.pdf", "spectra.pdf")
    # These changes affect the preamble and local figure path only.
    if profile == "xelatex":
        old = r"\setmainfont{texgyrepagella}[Extension=.otf,UprightFont=*-regular,ItalicFont=*-italic,BoldFont=*-bold,BoldItalicFont=*-bolditalic]"
        new = r"\setmainfont{texgyrepagella-regular.otf}[ItalicFont=texgyrepagella-italic.otf,BoldFont=texgyrepagella-bold.otf,BoldItalicFont=texgyrepagella-bolditalic.otf]"
        if old not in preamble:
            raise ValueError("Generated font preamble changed; inspect before packaging")
        preamble = preamble.replace(old, new)
    else:
        lines = preamble.splitlines()
        result = []
        removed = []
        for line in lines:
            if line == r"\usepackage{fontspec}":
                result.extend([r"\usepackage[T1]{fontenc}",
                               r"\usepackage[utf8]{inputenc}",
                               r"\usepackage{lmodern}"])
                removed.append("fontspec")
            elif line.startswith((r"\setmainfont", r"\setmonofont", r"\setmathfont")):
                removed.append("font command")
            elif line in (r"\usepackage{unicode-math}",
                           r"\AtBeginDocument{\let\setminus\smallsetminus}"):
                removed.append("unicode math")
            else:
                result.append(line)
        if len(removed) != 6:
            raise ValueError("Unexpected font preamble; inspect before packaging")
        preamble = "\n".join(result) + "\n"
    if body.replace("spectra.pdf", "c3-figures/spectra.pdf") != original_body:
        raise ValueError("Document body changed beyond the declared figure-path edit")
    tex = "% !TeX program = " + profile + "\n" + preamble.lstrip()
    tex += r"\begin{document}" + body
    includes = re.findall(r"\\(?:input|include)\s*\{([^}]+)\}", tex)
    if includes:
        raise ValueError("Unbundled TeX dependencies: " + repr(includes))
    if re.search(r"\\(?:bibliography|addbibresource)\b", tex):
        raise ValueError("External bibliography appeared; update the bundle manifest")
    if re.search(r"(?:(?<![A-Za-z0-9])[A-Za-z]:[\\/]|file://)", tex):
        raise ValueError("Local absolute path found in source")
    return tex


def compile_bundle(files, compiler, kind, output_dir):
    executable = Path(compiler).resolve()
    if not executable.is_file():
        found = shutil.which(compiler)
        if not found:
            raise ValueError("Compiler does not exist: " + compiler)
        executable = Path(found).resolve()
    version_result = subprocess.run([str(executable), "--version"],
                                    capture_output=True, text=True,
                                    encoding="utf-8", errors="replace", timeout=30)
    version = (version_result.stdout + version_result.stderr).splitlines()[0]
    validation_dir = output_dir / "validation"
    validation_dir.mkdir(exist_ok=True)
    logs = []
    with tempfile.TemporaryDirectory(prefix="hoggar-c3-source-check-") as tmp:
        stage = Path(tmp)
        for name, content in files.items():
            target = stage / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        if kind == "tectonic":
            command = [str(executable), "--untrusted", "--keep-logs", "--print", "main.tex"]
            passes = 1
        else:
            command = [str(executable), "-no-shell-escape", "-interaction=nonstopmode",
                       "-halt-on-error", "-file-line-error", "main.tex"]
            passes = 2
        returncode = 0
        for run in range(passes):
            completed = subprocess.run(command, cwd=stage, capture_output=True,
                                       text=True, encoding="utf-8", errors="replace",
                                       timeout=300)
            logs.append("Pass %d\n%s%s" % (run + 1, completed.stdout, completed.stderr))
            returncode = completed.returncode
            if returncode:
                break
        (validation_dir / "build.log").write_text("\n".join(logs), encoding="utf-8")
        if (stage / "main.log").exists():
            shutil.copyfile(stage / "main.log", validation_dir / "main.log")
        if returncode or not (stage / "main.pdf").exists():
            raise RuntimeError("Local compile failed; see " + str(validation_dir / "build.log"))
        pdf = (stage / "main.pdf").read_bytes()
        (validation_dir / "main.pdf").write_bytes(pdf)
    warnings = [line for line in "\n".join(logs).splitlines()
                if any(s in line for s in ("Missing character", "Undefined control",
                                           "Overfull", "warning:", "Fontconfig error"))]
    if any("Missing character" in line or "Undefined control" in line for line in warnings):
        raise RuntimeError("Typesetting lost glyphs or commands; inspect validation/build.log")
    return {"engine_kind": kind, "version": version,
            "binary_sha256": digest(executable.read_bytes()),
            "command": [executable.name] + command[1:], "returncode": returncode,
            "pdf_sha256": digest(pdf), "pdf_bytes": len(pdf),
            "warnings": warnings,
            "scope": "Local engine compilation only; not arXiv server acceptance or author approval."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("xelatex", "pdflatex"), default="xelatex")
    parser.add_argument("--compiler", help="Existing tectonic, xelatex or pdflatex executable")
    parser.add_argument("--compiler-kind", choices=("tectonic", "xelatex", "pdflatex"))
    parser.add_argument("--allow-draft", action="store_true",
                        help="Allow a source containing the explicit pending formal marker")
    args = parser.parse_args()
    raw = SOURCE.read_bytes()
    source = normalized(raw).decode("utf-8")
    build_record = json.loads((ROOT / "results/frontier-c3-paper-build.json").read_text(encoding="utf-8"))
    markdown_hash = digest(normalized(MARKDOWN.read_bytes()))
    if (build_record.get("tex_lf_sha256") != digest(normalized(raw)) or
            build_record.get("md_lf_sha256") != markdown_hash):
        parser.error("Generated TeX or Markdown differs from the paper build record; rebuild the main paper first")
    pending = "PENDING CONFIRMATION" in source
    if pending and not args.allow_draft:
        parser.error("Formal-verification placeholder remains; use --allow-draft for local layout testing only")
    tex = portable_tex(source, args.profile)
    readme = (
        "C3 preprint source bundle\n\n"
        "Title: Cospectral Pauli carriers with different completion spectra: "
        "an exact four-qubit C3 certificate\n"
        "Author: Alexander S. Donahue; 0thernes LLC\n"
        "Correspondence: 0_0@0thernes.art\n"
        "Research preprint; not peer reviewed. No submission/acceptance is implied.\n\n"
        "Top-level source: main.tex\nFigure: spectra.pdf\n"
        "Recommended processor for this bundle: " + args.profile + "\n"
        "Recommended arXiv distribution: TeX Live 2025.\n"
        "Select the processor in the submission form and inspect its compiled PDF.\n"
        "The bibliography is inline in main.tex; no external BibTeX file is required.\n"
        "No local system fonts, binaries, cache, generated main.pdf or TeX logs are included.\n"
        "The default XeLaTeX profile uses TeX Live font filenames, not OS font lookup.\n"
        "The optional pdfLaTeX profile uses Latin Modern/AMS fonts and changes typography.\n\n"
        "License: the unmodified project verification license is in anc/LICENSE.txt.\n"
        "This bundle does not grant CC BY or a general open-source license.\n"
        "The right holder must choose the platform's distribution license explicitly.\n"
        "Standard TeX packages/fonts are dependencies, not copied into this archive.\n"
        "No vendored third-party software is included.\n\n"
        "Research artifacts and AI disclosure: see the manuscript and the source project\n"
        "https://github.com/0thernes/hoggar-bound-lab\n"
        "The final release must identify its immutable commit and verification evidence.\n\n"
        "Formal marker present in this bundled source: " + str(pending) + "\n"
        "Human final approval and platform eligibility are separate from compilation.\n\n"
        "Official preparation rules checked " + POLICY_DATE + ":\n" +
        "\n".join(POLICIES.values()) + "\n"
    )
    files = {
        "main.tex": tex.encode("utf-8"),
        "spectra.pdf": FIGURE.read_bytes(),
        "anc/LICENSE.txt": normalized((ROOT / "LICENSE").read_bytes()),
        "anc/README.txt": readme.encode("utf-8"),
    }
    for name in files:
        if any(not re.fullmatch(r"[A-Za-z0-9_+.,=-]+", part)
               for part in Path(name).parts):
            raise ValueError("Non-portable archive filename: " + name)
    output_dir = ROOT / "build" / ("c3-arxiv-" + args.profile)
    output_dir.mkdir(parents=True, exist_ok=True)
    for name, content in files.items():
        dest = output_dir / "source" / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(content)
    archive = output_dir / ("c3-source-" + args.profile + ".zip")
    # Explicit allowlist and stable zip metadata: unrelated files are never packaged.
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as package:
        for name in sorted(files):
            entry = zipfile.ZipInfo(name, date_time=(2026, 11, 9, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            package.writestr(entry, files[name])
    validation = None
    if args.compiler:
        kind = args.compiler_kind or Path(args.compiler).stem.lower()
        if kind not in ("tectonic", "xelatex", "pdflatex"):
            parser.error("Set --compiler-kind for this executable")
        if kind == "pdflatex" and args.profile != "pdflatex":
            parser.error("The XeLaTeX profile needs a XeLaTeX engine")
        validation = compile_bundle(files, args.compiler, kind, output_dir)
    report = {
        "profile": args.profile, "recommended_arxiv_tex_live": "2025",
        "policy_checked": POLICY_DATE, "official_policy_urls": POLICIES,
        "source_tex_raw_sha256": digest(raw),
        "source_tex_lf_sha256": digest(normalized(raw)),
        "source_markdown_lf_sha256": markdown_hash,
        "paper_build_record_matches_source": True,
        "script_lf_sha256": digest(normalized(Path(__file__).read_bytes())),
        "document_body_changed": "Only figure path c3-figures/spectra.pdf -> spectra.pdf",
        "input_formal_placeholder_present": pending,
        "submission_status": "Not submitted; source packaging and local checks only",
        "author_final_approval_attested": False,
        "archive": archive.relative_to(ROOT).as_posix(),
        "archive_sha256": digest(archive.read_bytes()),
        "files": {name: {"sha256": digest(data), "bytes": len(data)}
                  for name, data in files.items()},
        "local_compile": validation,
        "arxiv_server_compile_checked": False,
        "pdflatex_compile_checked": bool(validation and validation["engine_kind"] == "pdflatex"),
    }
    report_path = ROOT / "results" / ("frontier-c3-source-bundle-" + args.profile + ".json")
    report_path.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print(json.dumps({"archive": str(archive), "report": str(report_path),
                      "draft": pending, "local_compile": validation is not None}, indent=2))


if __name__ == "__main__":
    main()
