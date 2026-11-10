#!/usr/bin/env python3
"""Make inline math in a Markdown file survive GitHub's renderer.

  python -I fix_github_math.py <file.md> [--write]

GitHub applies Markdown backslash escapes inside $...$ (so \, \{ \} \# are damaged), does not open math
after a quote or close it before ")" when the formula itself ends with ")", loses math inside *emphasis*
when it contains an underscore, pairs an underscore that follows punctuation in one formula with an
underscore that precedes punctuation in a later formula of the same paragraph (so both formulas are lost),
splits table cells at "|" inside math, and double-escapes < and >.
Spans at risk are rewritten to the code form $`...`$, which GitHub passes through verbatim; < and > become
\lt and \gt; "|" inside table-cell math becomes \vert.
"""
import re, sys

INLINE = re.compile(r"(?<![\\$`])\$(?!\s|`)([^$\n]+?)(?<!\s)\$")
CODEFORM = re.compile(r"\$`([^`\n]+)`\$")


def risky(tex, before, after, in_emphasis):
    if re.search(r"\\[^A-Za-z0-9\s]", tex):          # backslash + punctuation: \, \{ \} \# \; \! \|
        return "backslash-punctuation"
    if before in "\"'":
        return "quote before"
    if after == ")" and tex.rstrip().endswith(")"):
        return "paren after"
    if in_emphasis and "_" in tex:
        return "underscore inside emphasis"
    if re.search(r"[^\w\s]_|_[^\w\s]", tex):          # an underscore next to punctuation can open or close
        return "underscore next to punctuation"       # Markdown emphasis across two formulas of a paragraph
    return None


def fix_text(text):
    log = []
    out = []
    parts = re.split(r"(^```.*?^```[ \t]*$)", text, flags=re.S | re.M)
    for part in parts:
        if part.startswith("```"):
            out.append(part)
            continue
        lines = part.split("\n")
        for li, line in enumerate(lines):
            is_table = line.lstrip().startswith("|")
            in_emph = bool(re.match(r"^\*[^*].*\*$", line.strip()))      # a whole-line *caption*
            pieces = re.split(r"(\$`[^`\n]+`\$|`[^`\n]+`)", line)        # keep code spans and code-form math apart
            for pi, piece in enumerate(pieces):
                if piece.startswith("`") or piece.startswith("$`"):
                    continue
                def repl(m, piece=piece):
                    tex = m.group(1)
                    new = tex
                    if is_table and "|" in new:
                        new = re.sub(r"\s*\|\s*", r"\\vert ", new)
                    new = re.sub(r"\s*>\s*", r" \\gt ", new)
                    new = re.sub(r"\s*<\s*", r" \\lt ", new)
                    before = piece[m.start() - 1] if m.start() > 0 else " "
                    after = piece[m.end()] if m.end() < len(piece) else " "
                    why = risky(new, before, after, in_emph)
                    if why:
                        assert "`" not in new
                        res = "$`" + new + "`$"
                    else:
                        res = "$" + new + "$"
                    if res != m.group(0):
                        log.append((why or "operator", m.group(0), res))
                    return res
                pieces[pi] = INLINE.sub(repl, piece)
            lines[li] = "".join(pieces)
        out.append("\n".join(lines))
    return "".join(out), log


def main():
    path = sys.argv[1]
    sys.stdout.reconfigure(encoding="utf-8")
    text = open(path, encoding="utf-8").read()
    new, log = fix_text(text)
    for why, a, b in log:
        print("%-28s %s  ->  %s" % (why, a, b))
    print(len(log), "spans rewritten;", len(CODEFORM.findall(new)), "code-form spans in the result")
    again, log2 = fix_text(new)
    assert again == new and not log2, "not idempotent"
    if "--write" in sys.argv:
        open(path, "w", encoding="utf-8", newline="\n").write(new)
        print("written", path)


if __name__ == "__main__":
    main()
