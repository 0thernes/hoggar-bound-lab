# Portable C3 source bundle

The builder `publication/build_source_bundle.py` packages the generated paper without editing its canonical Markdown, the main PDF builder, or the mathematical body. It records hashes and changes only the font preamble and the relative figure path. Rebuild the main paper first: the script rejects a mismatch between current Markdown/TeX and `results/frontier-c3-paper-build.json`.

## Engine choice

Current arXiv documentation, checked 2026-11-09, supports both PDFLaTeX and XeLaTeX; TeX Live 2025 is its default distribution. XeLaTeX was added in November 2025. Its OpenType fonts must be loaded by filename, since general font-name lookup is unavailable. [Official engine and font requirements](https://info.arxiv.org/help/faq/texlive.html).

The default `xelatex` profile preserves the main paper's typography and explicitly names the TeX Gyre Pagella font files. Its math and monospace fonts also use filenames. All required font filenames are present in the official TeX Live 2025 font list; no font binary or local operating-system font is packaged. [Official font inventory](https://info.arxiv.org/help/faq/font-info-tl2025.html).

An optional `pdflatex` profile replaces `fontspec`/`unicode-math` with conventional Latin Modern and AMS fonts. This changes typography and page flow. Local Tectonic compilation of that profile is **not** a check by the actual pdfLaTeX engine; the report keeps that distinction explicit.

## Build

From the repository root, after the final paper is generated:

```powershell
python publication/build_source_bundle.py --compiler 'C:/Users/Alexa/AppData/Local/Temp/hoggar-paper-tools/tectonic/tectonic.exe'
```

For a different installation, supply the actual existing executable. The script also supports `--compiler /path/to/xelatex` and, with `--profile pdflatex`, an actual `pdflatex` executable. `--compiler-kind` disambiguates renamed executables. No large TeX installation is required by this builder.

The explicit `--allow-draft` option is only for a local test before the formal-verification placeholder has been removed. Such archives are marked draft in their manifest and README. It is not a submission-readiness override.

Example optional classic-font profile:

```powershell
python publication/build_source_bundle.py --profile pdflatex --compiler 'C:/Users/Alexa/AppData/Local/Temp/hoggar-paper-tools/tectonic/tectonic.exe'
```

## Files and validation boundary

The generated zip under `build/c3-arxiv-xelatex/` contains exactly:

```text
main.tex
spectra.pdf
anc/LICENSE.txt
anc/README.txt
```

The bibliography is inline in `main.tex`. The archive excludes its generated PDF, logs, caches, binaries, unused figures and unrelated repository files. arXiv requires the source for a TeX-generated paper and the figures needed to compile it; it does not require or accept a PDF-only workaround in this situation. Ancillary supporting files belong in `anc`. [Source rules](https://info.arxiv.org/help/submit_tex.html), [ancillary file rules](https://info.arxiv.org/help/ancillary_files.html).

`results/frontier-c3-source-bundle-xelatex.json` records input hashes, the exact allowlisted archive contents, compiler/version, local PDF hash and warnings. The corresponding profile-specific `validation/` directory retains its PDF and logs for inspection outside the submitted archive. Zip entry timestamps are fixed to make the archive reproducible from identical inputs. Licensing remains the unmodified custom verification license. No CC BY grant or platform submission agreement is silently selected.

Both draft profiles compiled locally with Tectonic 0.17.0. After the completed formal section was incorporated, the default XeLaTeX profile was regenerated and compiled again with exit code zero. Its archive SHA-256 is `c3627259a3ac7db5f5b565281df36bb09f124f69f1dd14fd6581b77eba6b151b`; the source hashes match the final paper build record, and no formal placeholder remains. The local log contains underfull-box notices and a Fontconfig initialization diagnostic, with no missing-character, undefined-control-sequence or overfull-box errors. This local diagnostic does not establish an arXiv server problem: fonts were explicitly loaded by filename. No actual pdfLaTeX binary was found in the inspected executable path, and no arXiv server compilation has been performed. The final canonical PDF has a separate all-nine-page visual review; the archive compiler's PDF has a distinct hash and should also be inspected in arXiv's own compilation interface.

The archive now includes the final formal paragraph. Regenerate it if subsequent human review changes the manuscript. During actual arXiv preparation select `main.tex`, the matching engine and TeX Live 2025, then review arXiv's own compiled PDF before finishing. Compilation, author approval, endorsement, license choice, moderation and announcement remain distinct steps. This builder performs no upload or submission.
