#!/usr/bin/env python3
"""
build_journal.py - the journal form of the paper: a main manuscript of about 10 000 words and a supplement.

  python scripts/build_journal.py --pandoc PATH --tectonic PATH

Derived mechanically from paper/spectral-floor.md, which stays the canonical text:

  main manuscript   Sections 1-8 and 11-12.  Sections 11 and 12 become 9 and 10; the labelled paragraphs of
                    Section 12 become "How the work was produced", "Data availability statement" and
                    "Acknowledgments" (with the AI disclosure statement, as IOP Publishing asks).
                    Figures 1 and 3 move to the end of Section 7.
  supplement        Section 9 (the demonstration on the Tsotchke stack), Section 10 (falsifiability and
                    replication) and the two appendices, as S1-S4, with the noise figure as Figure S1.

Cross-references are re-pointed.  Output in publication/spectral-floor/jphysa/: manuscript.tex/.pdf,
supplementary.tex/.pdf, figures/, word counts and hashes in build-record.json.  Nothing is submitted.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import build_latex as bl  # noqa: E402

ROOT = bl.ROOT
OUT = os.path.join(ROOT, "publication", "spectral-floor", "jphysa")
BS = "\\"
FIG = re.compile(r"!\[Figure (\d+)\]\(([^)]+)\)\s*\n\s*\n\*Figure \d+\.\s*([^\n]*)\*\n?")


def repoint_main(t):
    t = t.replace("Section 10", "@S2@").replace("Section 9", "@S1@")
    t = t.replace("Section 11", "Section 9").replace("Section 12", "Section 10")
    return t.replace("@S2@", "Supplementary Section S2").replace("@S1@", "Supplementary Section S1")


def split(body):
    parts = re.split(r"(?m)^(?=## )", body)
    main, supp = [], {}
    for p in parts:
        head = p.split("\n", 1)[0]
        if head.startswith("## 9."):
            supp["S1"] = p
        elif head.startswith("## 10."):
            supp["S2"] = p
        elif head.startswith("## Appendix A"):
            supp["S3"] = p
        elif head.startswith("## Appendix B"):
            supp["S4"] = p
        else:
            main.append(p)
    assert sorted(supp) == ["S1", "S2", "S3", "S4"], sorted(supp)
    main = "".join(main)

    # figures 1 and 3 go to the end of Section 7 of the main text; figure 2 stays in the supplement
    figs = {m.group(1): (m.group(2), m.group(3)) for m in FIG.finditer(supp["S1"])}
    assert sorted(figs) == ["1", "2", "3"], sorted(figs)
    supp["S1"] = FIG.sub(lambda m: m.group(0) if m.group(1) == "2" else "", supp["S1"])
    block = ("\nFigure 1 shows the floor of Table 1 against the earlier bound and the best assignments; Figure 2 shows the "
             "spectra just described.\n\n![Figure 1](%s)\n\n*Figure 1. %s*\n\n![Figure 2](%s)\n\n*Figure 2. %s*\n\n"
             % (figs["1"][0], figs["1"][1], figs["3"][0], figs["3"][1]))
    k = main.index("## 8. The Lean 4 development")
    main = main[:k] + block + main[k:]

    # Section 12 -> production paragraph, data availability, acknowledgments
    a = main.index("## 12. Disclosure, availability, licence")
    b = main.index("## References")
    sec12 = main[a:b]
    para = {}
    for label in ("How the work was produced", "AI disclosure statement", "Funding and competing interests",
                  "Data availability statement", "Licence"):
        m = re.search(r"\*\*%s\.\*\*\s*(.*?)(?=\n\n\*\*|\Z)" % re.escape(label), sec12, flags=re.S)
        assert m, label
        para[label] = m.group(1).strip()
    new12 = ("## 10. How the work was produced\n\n%s\n\n"
             "## Data availability statement\n\n%s\n\n"
             "## Acknowledgments\n\n**AI disclosure statement.** %s\n\n**Funding and competing interests.** %s\n\n"
             "**Licence of the supporting material.** %s\n\n"
             % (para["How the work was produced"], para["Data availability statement"], para["AI disclosure statement"],
                para["Funding and competing interests"], para["Licence"]))
    main = main[:a] + new12 + main[b:]
    main = main.replace("## 11. Limitations and open problems", "## 9. Limitations and open problems")
    main = repoint_main(main)
    assert "Appendix" not in main.split("## References")[0], "main text still points to an appendix"

    titles = {"S1": "## S1. A running example on the Tsotchke stack", "S2": "## S2. Falsifiability and replication",
              "S3": "## S3. Reproduction", "S4": "## S4. Witness assignments"}
    out = []
    for key in ("S1", "S2", "S3", "S4"):
        text = titles[key] + "\n" + supp[key].split("\n", 1)[1]
        text = text.replace("Section 10", "@S2@").replace("Section 9", "@S1@")
        text = text.replace("@S2@", "Section S2").replace("@S1@", "Section S1").replace("Figure 2", "Figure S1")
        out.append(text)
    return main, "".join(out)


def words(md):
    t = re.sub(r"```.*?```", " ", md, flags=re.S)
    t = re.sub(r"\$`[^`]*`\$|\$[^$\n]*\$", " M ", t)
    return len(re.findall(r"[A-Za-z0-9][A-Za-z0-9\-]*", t))


def compile_tex(tectonic, name, record):
    run = subprocess.run([tectonic, "--untrusted", "--keep-logs", name + ".tex"], cwd=OUT, capture_output=True, text=True,
                         encoding="utf-8", errors="replace")
    log = run.stdout + run.stderr
    open(os.path.join(OUT, name + "-tectonic.log"), "w", encoding="utf-8", newline="\n").write(log)
    if run.returncode != 0:
        print(log[-3000:])
        sys.exit("tectonic failed on " + name)
    pdf = os.path.join(OUT, name + ".pdf")
    record[name + "_pdf_sha256"] = hashlib.sha256(open(pdf, "rb").read()).hexdigest()
    record[name + "_overfull_pt"] = sorted(set(re.findall(r"Overfull \\hbox \(([0-9.]+)pt too wide\)", log)), key=float)[-4:]
    for ext in (".log", ".aux", ".out"):
        f = os.path.join(OUT, name + ext)
        if os.path.exists(f):
            os.remove(f)
    return os.path.getsize(pdf)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pandoc", default=shutil.which("pandoc"))
    ap.add_argument("--tectonic", default=shutil.which("tectonic"))
    args = ap.parse_args()
    if not args.pandoc:
        ap.error("supply --pandoc (and --tectonic to compile)")
    text = open(bl.SRC, encoding="utf-8").read()
    title, subtitle, byline, note, abstract, body = bl.split_source(text)
    main_md, supp_md = split(body)
    os.makedirs(os.path.join(OUT, "figures"), exist_ok=True)
    for f in sorted(os.listdir(os.path.join(ROOT, "paper", "figures"))):
        if f.endswith(".png"):
            shutil.copyfile(os.path.join(ROOT, "paper", "figures", f), os.path.join(OUT, "figures", f))
    tex = lambda s: bl.pandoc(args.pandoc, s).strip()
    who, _, mail = byline[0].partition("Correspondence:")
    who, _, orcid = who.partition("ORCID:")
    name, _, affiliation = who.strip().rstrip(".").partition(",")
    author = "%s%s%s %s%s%s " % (tex(name), BS, BS, tex(affiliation.strip()), BS, BS)
    if orcid.strip():
        author += "ORCID %s%s%s " % (tex(orcid.strip().rstrip(".")), BS, BS)
    author += "%stexttt{%s}" % (BS, mail.strip().replace("_", BS + "_"))
    record = {"source": "paper/spectral-floor.md", "source_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
              "words_main_with_abstract_and_references": words(abstract) + words(main_md),
              "words_main_text_only": words(main_md.split("## References")[0]),
              "words_abstract": words(abstract), "words_supplement": words(supp_md)}

    doc = [bl.PREAMBLE,
           "%stitle{%s}" % (BS, tex(title)), "%sauthor{%s}" % (BS, author), "%sdate{}" % BS,
           "%sbegin{document}" % BS, "%smaketitle" % BS,
           bl.pandoc(args.pandoc, repoint_main(note)),
           "%sbegin{abstract}" % BS, bl.pandoc(args.pandoc, abstract), "%send{abstract}" % BS,
           bl.fit_tables(bl.pandoc(args.pandoc, bl.prepare(main_md))), "%send{document}" % BS, ""]
    open(os.path.join(OUT, "manuscript.tex"), "w", encoding="utf-8", newline="\n").write("\n".join(doc))

    head = ("Supplementary material for the manuscript of the same title. Section, theorem, proposition and table numbers "
            "without the prefix S refer to the main text.")
    sdoc = [bl.PREAMBLE,
            "%srenewcommand{%sthefigure}{S%sarabic{figure}}" % (BS, BS, BS),
            "%stitle{Supplementary material%s%s[0.5em]%slarge %s}" % (BS, BS, BS, BS, tex(title)),
            "%sauthor{%s}" % (BS, tex(name)), "%sdate{}" % BS, "%sbegin{document}" % BS, "%smaketitle" % BS,
            head, "", bl.fit_tables(bl.pandoc(args.pandoc, bl.prepare(supp_md))), "%send{document}" % BS, ""]
    open(os.path.join(OUT, "supplementary.tex"), "w", encoding="utf-8", newline="\n").write("\n".join(sdoc))
    print("words: main text %d, abstract %d, with references %d; supplement %d"
          % (record["words_main_text_only"], record["words_abstract"], record["words_main_with_abstract_and_references"],
             record["words_supplement"]))
    if args.tectonic:
        for nm in ("manuscript", "supplementary"):
            size = compile_tex(args.tectonic, nm, record)
            print("wrote", nm + ".pdf", size, "bytes; widest overfull boxes (pt):", record[nm + "_overfull_pt"])
        record["tectonic"] = subprocess.check_output([args.tectonic, "--version"], text=True).strip()
    record["pandoc"] = subprocess.check_output([args.pandoc, "--version"], text=True).splitlines()[0]
    json.dump(record, open(os.path.join(OUT, "build-record.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
