#!/usr/bin/env python3
"""
build_paper.py - turns paper/spectral-floor.md into a standalone HTML page (MathJax) and, when a
Chromium-based browser is available, a PDF.

  python scripts/build_paper.py            # writes paper/spectral-floor.html, docs/index.html, paper/spectral-floor.pdf

The Markdown source is the canonical text (GitHub renders it directly). Mathematics is written as
$...$ or $`...`$ inline and as fenced ```math blocks; all are protected from the Markdown parser here.
Needs the `commonmark` Python package.
"""
import base64, html, os, re, shutil, subprocess, sys

import commonmark

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "paper", "spectral-floor.md")
OUT_HTML = os.path.join(ROOT, "paper", "spectral-floor.html")
OUT_PDF = os.path.join(ROOT, "paper", "spectral-floor.pdf")
DOCS = os.path.join(ROOT, "docs")
AUTHOR = "Donahue, Alexander S."
INSTITUTION = "0thernes LLC"
SITE = "https://0thernes.github.io/hoggar-bound-lab/"

CSS = """
:root{--bg:#fbfaf7;--ink:#1b1f27;--muted:#5b6370;--rule:#d9d6cc;--accent:#0f7a62;--code:#f1efe8;--note:#f3f1e9}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#14171c;--ink:#e6e3da;--muted:#9aa3b0;--rule:#2f353f;--accent:#5ef2c8;--code:#1d2128;--note:#1a1e25}}
:root[data-theme="dark"]{--bg:#14171c;--ink:#e6e3da;--muted:#9aa3b0;--rule:#2f353f;--accent:#5ef2c8;--code:#1d2128;--note:#1a1e25}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--ink);font:17px/1.58 "Iowan Old Style","Palatino Linotype",Palatino,Georgia,serif}
main{max-width:46rem;margin:0 auto;padding:2.5rem 16px 5rem}
h1{font-size:2rem;line-height:1.2;margin:0 0 .6rem;letter-spacing:-.01em;text-wrap:balance}
h2{font-size:1.32rem;margin:2.6rem 0 .7rem;padding-top:.9rem;border-top:1px solid var(--rule)}
h3{font-size:1.08rem;margin:1.8rem 0 .5rem}
p{margin:.75rem 0}
a{color:var(--accent);text-decoration-thickness:1px;text-underline-offset:2px}
blockquote{margin:1.2rem 0;padding:.7rem 1rem;background:var(--note);border-left:3px solid var(--accent);font-size:.95em}
blockquote p{margin:.35rem 0}
code{font:0.86em/1.4 ui-monospace,"Cascadia Mono",Consolas,Menlo,monospace;background:var(--code);padding:.08em .3em;border-radius:3px}
pre{background:var(--code);padding:.8rem 1rem;border-radius:6px;overflow-x:auto;font-size:.84rem;line-height:1.45}
pre code{background:none;padding:0;font-size:inherit}
.tablewrap{overflow-x:auto;margin:1rem 0}
table{border-collapse:collapse;font-size:.88rem;line-height:1.35;min-width:100%;font-variant-numeric:tabular-nums}
th,td{padding:.38rem .6rem;border-bottom:1px solid var(--rule);text-align:left;vertical-align:top}
th{font-weight:600;border-bottom:2px solid var(--ink);white-space:nowrap}
img{max-width:100%;height:auto;display:block;margin:1.2rem auto .3rem;background:#fff;border-radius:4px}
em{color:inherit}
.MathJax{font-size:1em!important}
mjx-container[display="true"]{overflow-x:auto;overflow-y:hidden;padding:.2rem 0}
ul{padding-left:1.3rem}
li{margin:.3rem 0}
.byline{color:var(--muted);font-size:.95rem}
@media print{:root:not([data-theme="dark"]):not(.x){--bg:#fff;--ink:#000;--muted:#444;--rule:#bbb;--accent:#0b5c4a;--code:#f3f3f1;--note:#f6f5f0}body{font-size:11pt;background:#fff;color:#000}main{max-width:none;padding:0}h2{break-after:avoid}pre,table,blockquote,img{break-inside:avoid}a{color:#000}}
"""

MATHJAX = """<script>
window.MathJax = {tex: {inlineMath: [['\\\\(', '\\\\)']], displayMath: [['\\\\[', '\\\\]']]}, options: {skipHtmlTags: ['script','noscript','style','textarea','pre','code']},
  startup: {pageReady: () => MathJax.startup.defaultPageReady().then(() => { document.documentElement.setAttribute('data-math', 'ready'); })}};
</script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-chtml-full.min.js"
  integrity="sha384-dCtf/9Xgzj8edI30iIEsxNfjUQ0zj2AXa3eUdgjsx8odUmpURZx5Z7aDZmV781et" crossorigin="anonymous"></script>"""


def protect_math(text):
    """Replace math by placeholders; returns (text, store)."""
    store = []

    def keep(tex, display):
        store.append((tex, display))
        return "M%d" % (len(store) - 1)   # private-use delimiters survive the Markdown parser

    out = []
    parts = re.split(r"(^```.*?^```[ \t]*$)", text, flags=re.S | re.M)
    for part in parts:
        if part.startswith("```"):
            first, rest = part.split("\n", 1)
            if first.strip() == "```math":
                body = rest.rsplit("```", 1)[0]
                out.append("\n" + keep(body.strip(), True) + "\n")
            else:
                out.append(part)          # ordinary code block: untouched
            continue
        # GitHub's code form of inline math, $`...`$, which its renderer passes through verbatim; the
        # source uses it wherever plain $...$ would be damaged there (backslash-punctuation such as \, \{ \#,
        # a formula ending in ")" before ")", math after a quote or inside *emphasis*)
        part = re.sub(r"\$`([^`\n]+)`\$", lambda m: keep(m.group(1), False), part)
        # inline code spans must not be searched for math
        pieces = re.split(r"(`[^`\n]+`)", part)
        for i, piece in enumerate(pieces):
            if piece.startswith("`"):
                continue
            piece = re.sub(r"\$\$(.+?)\$\$", lambda m: keep(m.group(1).strip(), True), piece, flags=re.S)
            piece = re.sub(r"(?<![\\$])\$(?!\s)([^$\n]+?)(?<!\s)\$", lambda m: keep(m.group(1), False), piece)
            pieces[i] = piece
        out.append("".join(pieces))
    return "".join(out), store


def restore_math(htmltext, store):
    def put(m):
        tex, display = store[int(m.group(1))]
        tex = html.escape(tex, quote=False)
        return ("\\[" + tex + "\\]") if display else ("\\(" + tex + "\\)")
    return re.sub("M(\\d+)", put, htmltext)


def inline_html(md):
    out = commonmark.commonmark(md).strip()
    if out.startswith("<p>") and out.endswith("</p>"):
        out = out[3:-4]
    return out


def convert_tables(text):
    lines = text.split("\n")
    res, i = [], 0
    while i < len(lines):
        if lines[i].lstrip().startswith("|") and i + 1 < len(lines) and re.match(r"^\s*\|[\s:|-]+\|\s*$", lines[i + 1]):
            block = []
            while i < len(lines) and lines[i].lstrip().startswith("|"):
                block.append(lines[i]); i += 1
            def cells(row):
                return [c.strip() for c in row.strip().strip("|").split("|")]
            head = cells(block[0]); body = [cells(r) for r in block[2:]]
            h = "<div class=\"tablewrap\"><table><thead><tr>" + "".join("<th>%s</th>" % inline_html(c) for c in head) + "</tr></thead><tbody>"
            for row in body:
                h += "<tr>" + "".join("<td>%s</td>" % inline_html(c) for c in row) + "</tr>"
            h += "</tbody></table></div>"
            res.append(""); res.append(h); res.append("")
        else:
            res.append(lines[i]); i += 1
    return "\n".join(res)


def build(embed_images=False):
    src = open(SRC, encoding="utf-8").read()
    title = re.search(r"^# (.+)$", src, flags=re.M).group(1)
    text, store = protect_math(src)
    text = convert_tables(text)
    body = commonmark.commonmark(text)
    body = restore_math(body, store)
    if embed_images:
        def emb(m):
            path = os.path.join(ROOT, "paper", m.group(1))
            if not os.path.exists(path):
                return m.group(0)
            data = base64.b64encode(open(path, "rb").read()).decode()
            return 'src="data:image/png;base64,%s"' % data
        body = re.sub(r'src="(figures/[^"]+)"', emb, body)
    # bibliographic metadata for indexing services (Highwire Press and Dublin Core tags, as read by Google Scholar)
    m = re.search(r"version ([0-9.]+), (\d+) (\w+) (\d{4})", src)
    months = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October",
              "November", "December"]
    date = "%s/%02d/%02d" % (m.group(4), months.index(m.group(3)) + 1, int(m.group(2)))
    tags = [("citation_title", title), ("citation_author", AUTHOR), ("citation_author_institution", INSTITUTION),
            ("citation_publication_date", date), ("citation_online_date", date),
            ("citation_technical_report_institution", INSTITUTION),
            ("citation_technical_report_number", "Hoggar Bound Lab, version " + m.group(1)),
            ("citation_pdf_url", SITE + "paper/spectral-floor.pdf"), ("citation_abstract_html_url", SITE),
            ("citation_language", "en"),
            ("DC.title", title), ("DC.creator", AUTHOR), ("DC.publisher", INSTITUTION), ("DC.date", date.replace("/", "-")),
            ("DC.type", "Text"), ("DC.language", "en"), ("author", "Alexander S. Donahue (%s)" % INSTITUTION)]
    meta = "\n".join('<meta name="%s" content="%s">' % (k, html.escape(v, quote=True)) for k, v in tags)
    page = ("<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
            "<title>Spectral Floor, Machine-Checked</title>\n"
            "<meta name=\"description\" content=\"%s\">\n%s\n<style>%s</style>\n%s\n</head>\n<body>\n<main>\n%s\n</main>\n</body>\n</html>\n"
            % (html.escape(title), meta, CSS, MATHJAX, body))
    return page


def find_browser():
    for cand in (r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
                 r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
                 r"C:\Program Files\Google\Chrome\Application\chrome.exe",
                 "/usr/bin/chromium", "/usr/bin/chromium-browser", "/usr/bin/google-chrome"):
        if os.path.exists(cand):
            return cand
    return shutil.which("chromium") or shutil.which("google-chrome") or shutil.which("msedge")


def main():
    page = build(embed_images=False)
    open(OUT_HTML, "w", encoding="utf-8", newline="\n").write(page)
    os.makedirs(DOCS, exist_ok=True)
    single = build(embed_images=True)
    open(os.path.join(DOCS, "index.html"), "w", encoding="utf-8", newline="\n").write(single)
    open(os.path.join(DOCS, ".nojekyll"), "w").write("")
    print("wrote", OUT_HTML, "and docs/index.html (%d bytes)" % len(single))
    browser = find_browser()
    if not browser or "--no-pdf" in sys.argv:
        print("no browser found (or --no-pdf): PDF not built"); return
    url = "file:///" + os.path.join(DOCS, "index.html").replace("\\", "/").replace(" ", "%20")
    tmp_profile = os.path.join(ROOT, "build", "pdf-profile")
    os.makedirs(tmp_profile, exist_ok=True)
    cmd = [browser, "--headless=new", "--disable-gpu", "--no-pdf-header-footer", "--user-data-dir=" + tmp_profile,
           "--virtual-time-budget=45000", "--run-all-compositor-stages-before-draw", "--print-to-pdf=" + OUT_PDF, url]
    subprocess.run(cmd, check=False, timeout=180, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if os.path.exists(OUT_PDF):
        shutil.copyfile(OUT_PDF, os.path.join(DOCS, "spectral-floor.pdf"))
        print("wrote", OUT_PDF, os.path.getsize(OUT_PDF), "bytes")
    else:
        print("PDF was not produced")


if __name__ == "__main__":
    main()
