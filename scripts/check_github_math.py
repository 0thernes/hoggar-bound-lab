#!/usr/bin/env python3
"""
check_github_math.py - checks that every formula in the Markdown sources reaches GitHub's math renderer
unchanged.

  python scripts/check_github_math.py [file.md ...]      (default: README.md paper/spectral-floor.md)

GitHub runs Markdown over the text before MathJax sees it. Inside $...$ it applies backslash escapes
(\, \{ \} \# lose their backslash), it does not recognise some spans at all (after a quote, before ")"
when the formula ends in ")", with an underscore inside *emphasis*), it splits table cells at "|", and
it double-escapes < and >. The sources therefore use the code form $`...`$ for such formulas, \lt and
\gt for the two relations, \vert inside tables, and fenced ```math blocks for displays.

The script sends each file to GitHub's Markdown API (needs the `gh` CLI, logged in, and network access),
extracts what the renderer will typeset, and compares it with the formulas found by build_paper.py.
Exit status 1 if any formula differs, is missing, or a stray dollar sign is left in the text.
"""
import collections, html, json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import build_paper as bp


def check(rel):
    src = open(os.path.join(ROOT, rel), encoding="utf-8").read()
    _, store = bp.protect_math(src)
    body = json.dumps({"text": src, "mode": "gfm"})
    r = subprocess.run(["gh", "api", "markdown", "--method", "POST", "--input", "-"],
                       input=body.encode("utf-8"), capture_output=True)
    if r.returncode != 0:
        print("%s: GitHub API call failed: %s" % (rel, r.stderr.decode("utf-8", "replace")[:300]))
        return False
    out = r.stdout.decode("utf-8", "replace")
    rendered = []
    for m in re.finditer(r"<math-renderer[^>]*>(.*?)</math-renderer>", out, flags=re.S):
        s = html.unescape(m.group(1)).strip()
        rendered.append(s[2:-2] if s.startswith("$$") else s[1:-1])
    norm = lambda s: re.sub(r"\s+", " ", s).strip()
    want = collections.Counter(norm(t) for t, _ in store)
    got = collections.Counter(norm(t) for t in rendered)
    missing, extra = want - got, got - want
    rest = re.sub(r"<math-renderer[^>]*>.*?</math-renderer>", "", out, flags=re.S)
    rest = re.sub(r"<pre.*?</pre>|<code.*?</code>", "", rest, flags=re.S)
    stray = re.findall(r".{0,40}\$.{0,40}", html.unescape(re.sub(r"<[^>]+>", "", rest)))
    double = out.count("&amp;gt;") + out.count("&amp;lt;")
    good = not (missing or extra or stray or double)
    print("%s  %s: %d formulas in the source, %d at the renderer, %d altered or missing, %d stray dollar signs, %d double-escaped relations"
          % ("PASS" if good else "FAIL", rel, len(store), len(rendered), sum(missing.values()), len(stray), double))
    for k in list(missing)[:20]:
        print("    source:   ", k[:150])
    for k in list(extra)[:20]:
        print("    rendered: ", k[:150])
    for k in stray[:10]:
        print("    stray:    ", k.replace("\n", " "))
    return good


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    files = sys.argv[1:] or ["README.md", "paper/spectral-floor.md"]
    results = [check(f) for f in files]
    sys.exit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
