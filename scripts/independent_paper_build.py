"""Typeset the independent companion with Pandoc and Tectonic.

Requires Python 3.9+, Pandoc, and Tectonic; no Python packages are needed.
Official portable releases used for the audited build:
  Pandoc 3.13: https://github.com/jgm/pandoc/releases/tag/3.13
  Tectonic 0.17.0: https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.17.0
Pass --pandoc and --tectonic if the executables are not on PATH.
Tectonic downloads its TeX packages into its normal local cache on first use.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
RESULTS = ROOT / "results"
STEM = "independent-research-note"

PREAMBLE = r"""
\documentclass[11pt,letterpaper]{article}
\usepackage[margin=0.86in,top=0.8in,bottom=0.86in,headheight=15pt]{geometry}
\usepackage{fontspec}
\setmainfont{texgyrepagella}[Extension=.otf,UprightFont=*-regular,ItalicFont=*-italic,BoldFont=*-bold,BoldItalicFont=*-bolditalic]
\setmonofont{lmmono10-regular.otf}[Scale=0.86]
\usepackage{amsmath,amssymb}
\usepackage{unicode-math}
\setmathfont{texgyrepagella-math.otf}
\AtBeginDocument{\let\setminus\smallsetminus}
\usepackage{microtype}
\usepackage{graphicx}
\usepackage{float}
\usepackage[font=small,labelfont=bf]{caption}
\usepackage{placeins}
\usepackage{needspace}
\usepackage{longtable,booktabs,array,calc}
\usepackage{xcolor}
\definecolor{Accent}{HTML}{1B4965}
\definecolor{Muted}{HTML}{58656D}
\usepackage{xurl}
\usepackage{hyperref}
\usepackage{bookmark}
\hypersetup{colorlinks=true,urlcolor=Accent,linkcolor=Accent,citecolor=Accent,
pdftitle={A verified spectral bound for Pauli contextuality: independent validation and critical synthesis},
pdfauthor={Hoggar Bound Lab; AI-assisted research artifact},
pdfsubject={Independent verification companion; research preprint, not peer reviewed}}
\urlstyle{same}
\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\color{Muted}HOGGAR BOUND LAB}
\fancyhead[R]{\small\color{Muted}Independent validation}
\fancyfoot[L]{\footnotesize\color{Muted}Research preprint \textbullet\ 2026-11-09}
\fancyfoot[R]{\footnotesize\color{Muted}\thepage}
\renewcommand{\headrulewidth}{0.25pt}
\renewcommand{\footrulewidth}{0pt}
\usepackage{titlesec}
\titleformat{\section}{\large\bfseries\color{Accent}}{}{0pt}{}
\titlespacing*{\section}{0pt}{1.05em}{0.4em}
\setcounter{secnumdepth}{-2}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.45em}
\setlength{\emergencystretch}{3em}
\widowpenalty=10000
\clubpenalty=10000
\brokenpenalty=10000
\setlength{\LTleft}{0pt}
\setlength{\LTright}{0pt}
\setlength{\tabcolsep}{4pt}
\renewcommand{\arraystretch}{1.14}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\begin{document}
\thispagestyle{empty}
{\small\bfseries\color{Accent}INDEPENDENT VERIFICATION COMPANION}\par
\vspace{0.6em}
{\fontsize{22}{25}\selectfont\bfseries A verified spectral bound\\for Pauli contextuality}\par
\vspace{0.25em}
{\large\color{Accent}Independent validation and critical synthesis}\par
\vspace{0.8em}
{\normalsize Hoggar Bound Lab; AI-assisted research artifact}\par
{\small\color{Muted}2026-11-09 \quad\textbullet\quad Research preprint, not peer reviewed}\par
\vspace{0.6em}
{\color{Accent}\hrule height 0.65pt}
\vspace{0.5em}
"""


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pandoc", default=shutil.which("pandoc"))
    parser.add_argument("--tectonic", default=shutil.which("tectonic"))
    args = parser.parse_args()
    if not args.pandoc or not args.tectonic:
        parser.error("Pandoc and Tectonic must be on PATH or supplied explicitly")
    source = PAPER / (STEM + ".md")
    markdown = source.read_text(encoding="utf-8")
    body = "## Abstract" + markdown.split("## Abstract", 1)[1]
    # Headers and identity are typeset once in the document preamble.
    converted = subprocess.run(
        [args.pandoc, "--from=markdown+tex_math_dollars+tex_math_single_backslash",
         "--to=latex", "--wrap=none", "--shift-heading-level-by=-1"],
        input=body, text=True, encoding="utf-8", capture_output=True, check=True)
    fragment = converted.stdout
    # Pandoc 3.13's captionless-table marker requires a newer caption package
    # than Tectonic's pinned bundle. The table has no caption or references.
    fragment = fragment.replace(r"\def\LTcaptype{none}", r"\def\LTcaptype{table}")
    # Give the descriptive first column adequate width; the four numeric
    # columns remain equally sized. The source has one five-column table.
    fragment = fragment.replace(r"\real{0.1579}", r"\real{0.3200}")
    fragment = fragment.replace(r"\real{0.2105}", r"\real{0.1700}")
    fragment = fragment.replace("independent-figures/spectral-bounds.png",
                                "independent-figures/spectral-bounds.pdf")
    fragment = fragment.replace(r"\begin{figure}", r"\begin{figure}[H]")
    fragment = fragment.replace("The zero-support case is trivial.",
                                "\\Needspace{7\\baselineskip}\nThe zero-support case is trivial.")
    fragment = fragment.replace(r"\section{4. Formal verification boundary}",
                                "\\FloatBarrier\n\\section{4. Formal verification boundary}")
    fragment = fragment.replace(r"\section{References and evidence}",
                                "\\clearpage\n\\section{References and evidence}")
    fragment = re.sub(r"\\texttt\{((?:results|tests|HoggarBound)/[^}]*)\}",
                      lambda m: "\\path{" + m.group(1).replace(r"\_", "_") + "}",
                      fragment)
    tex = PREAMBLE + fragment + "\n\\end{document}\n"
    tex_path = PAPER / (STEM + ".tex")
    tex_path.write_text(tex, encoding="utf-8")
    # A simple temporary path avoids TeX filename parsing issues with brackets.
    with tempfile.TemporaryDirectory(prefix="hoggar-independent-paper-") as tmp:
        staged = Path(tmp) / (STEM + ".tex")
        staged.write_text(tex, encoding="utf-8")
        figures = PAPER / "independent-figures"
        if figures.exists():
            shutil.copytree(figures, Path(tmp) / "independent-figures")
        print("Typesetting; TeX package downloads and diagnostics are recorded in the build log.", flush=True)
        with (RESULTS / "independent-paper-build.log").open("w", encoding="utf-8") as logfile:
            run = subprocess.Popen(
                [args.tectonic, "--untrusted", "--keep-logs", "--print", str(staged)],
                cwd=tmp, text=True, encoding="utf-8", errors="replace",
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            for line in run.stdout:
                logfile.write(line)
                logfile.flush()
                if line.startswith(("error:", "warning:", "note: Running", "note: Writing")):
                    print(line.rstrip(), flush=True)
            code = run.wait()
        if code:
            raise SystemExit(code)
        pdf = Path(tmp) / (STEM + ".pdf")
        shutil.copyfile(pdf, PAPER / pdf.name)
        engine_log = Path(tmp) / (STEM + ".log")
        if engine_log.exists():
            shutil.copyfile(engine_log, RESULTS / "independent-paper-tex.log")
    report = {
        "pandoc": subprocess.check_output([args.pandoc, "--version"], text=True).splitlines()[0],
        "tectonic": subprocess.check_output([args.tectonic, "--version"], text=True).strip(),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "tex_sha256": hashlib.sha256(tex_path.read_bytes()).hexdigest(),
        "source_lf_sha256": hashlib.sha256(source.read_bytes().replace(b"\r\n", b"\n")).hexdigest(),
        "tex_lf_sha256": hashlib.sha256(tex_path.read_bytes().replace(b"\r\n", b"\n")).hexdigest(),
        "text_hash_normalization": "Raw hashes describe local bytes; LF hashes replace CRLF with LF to match Git text normalization.",
        "pdf_sha256": hashlib.sha256((PAPER / (STEM + ".pdf")).read_bytes()).hexdigest(),
        "pdf_bytes": (PAPER / (STEM + ".pdf")).stat().st_size,
        "pandoc_binary_sha256": hashlib.sha256(Path(args.pandoc).read_bytes()).hexdigest(),
        "tectonic_binary_sha256": hashlib.sha256(Path(args.tectonic).read_bytes()).hexdigest(),
        "trusted_content": "Local independent research note; TeX insecure features disabled",
    }
    (RESULTS / "independent-paper-build.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
