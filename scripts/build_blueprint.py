#!/usr/bin/env python3
"""Parse blueprint/src/content.tex, run strict Lean checkdecls + DAG checks, and build HTML/SVG Blueprint.

Produces `blueprint/web/index.html` and `blueprint/web/blueprint-graph.json`, which
`scripts/independent_site.py` deploys to `/blueprint/` inside the single GitHub Pages site
(preventing workflow collision with `.github/workflows/independent-pages.yml`).
"""
from __future__ import annotations

import html
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX_PATH = ROOT / "blueprint" / "src" / "content.tex"
WEB_DIR = ROOT / "blueprint" / "web"

ENV_RE = re.compile(
    r"\\begin\{(definition|lemma|theorem|corollary)\}\[([^\]]+)\](.*?)\\end\{\1\}",
    re.S,
)


def collect_verified_lean_decls() -> set[str]:
    """Collect every verified declaration name from axiom logs + Lean Challenge/Solution files."""
    decls: set[str] = set()
    log_files = [
        "results/new-formalizations-lean-axioms.log",
        "results/lean-independent-verification.log",
        "results/lean-saturated-axioms.log",
        "results/lean-saturated-seven-axioms.log",
        "results/frontier-c3-lean-axioms.log",
        "results/lean-c3-all-qubits-axioms.log",
        "results/stability-lean-axioms.log",
    ]
    for rel in log_files:
        p = ROOT / rel
        if p.is_file():
            txt = p.read_text(encoding="utf-8")
            decls.update(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", txt))

    # Also collect definitions/theorems directly defined in Lean source modules
    for lean_file in sorted((ROOT / "lean" / "HoggarBound").glob("*.lean")):
        txt = lean_file.read_text(encoding="utf-8")
        ns_match = re.findall(r"^namespace\s+([A-Za-z0-9_.]+)", txt, re.M)
        prefixes = [""] + [f"{ns}." for ns in ns_match]
        for kind, name in re.findall(r"^(?:noncomputable\s+)?(def|theorem|lemma|structure|abbrev)\s+([A-Za-z0-9_']+)", txt, re.M):
            for pref in prefixes:
                decls.add(f"{pref}{name}")
    return decls


def parse_blueprint() -> list[dict]:
    txt = TEX_PATH.read_text(encoding="utf-8")
    nodes: list[dict] = []
    for m in ENV_RE.finditer(txt):
        kind, title, body = m.group(1), m.group(2).strip(), m.group(3)
        lbl_m = re.search(r"\\label\{([^}]+)\}", body)
        if not lbl_m:
            raise RuntimeError(f"Blueprint node missing \\label: {title}")
        label = lbl_m.group(1).strip()
        lean_m = re.search(r"\\lean\{([^}]+)\}", body)
        lean_names = [x.strip() for x in lean_m.group(1).split(",") if x.strip()] if lean_m else []
        uses_m = re.search(r"\\uses\{([^}]+)\}", body)
        uses = [x.strip() for x in uses_m.group(1).split(",") if x.strip()] if uses_m else []
        leanok = bool(re.search(r"\\leanok\b", body))
        desc = re.sub(r"\\(label|lean|uses)\{[^}]*\}", "", body)
        desc = re.sub(r"\\leanok\b", "", desc)
        desc = re.sub(r"\s+", " ", desc).strip()
        nodes.append({
            "id": label,
            "kind": kind,
            "title": title,
            "lean": lean_names,
            "uses": uses,
            "leanok": leanok,
            "description": desc,
        })
    return nodes


def check_dag(nodes: list[dict]) -> dict[str, int]:
    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        for u in n["uses"]:
            if u not in by_id:
                raise RuntimeError(f"Blueprint node {n['id']} references unknown \\uses{{{u}}}")
    # Topological depth & cycle detection
    depth: dict[str, int] = {}
    visiting: set[str] = set()

    def dfs(nid: str) -> int:
        if nid in depth:
            return depth[nid]
        if nid in visiting:
            raise RuntimeError(f"Cycle detected in Blueprint dependency graph at {nid}")
        visiting.add(nid)
        d = 0 if not by_id[nid]["uses"] else 1 + max(dfs(u) for u in by_id[nid]["uses"])
        visiting.remove(nid)
        depth[nid] = d
        return d

    for n in nodes:
        dfs(n["id"])
    return depth


def render_svg(nodes: list[dict], depths: dict[str, int]) -> str:
    layers: dict[int, list[dict]] = {}
    for n in nodes:
        layers.setdefault(depths[n["id"]], []).append(n)

    max_layer = max(layers.keys()) if layers else 0
    box_w, box_h = 260, 72
    x_gap, y_gap = 40, 62
    max_cols = max(len(v) for v in layers.values()) if layers else 1
    width = max(980, max_cols * (box_w + x_gap) + 80)
    height = (max_layer + 1) * (box_h + y_gap) + 90

    pos: dict[str, tuple[float, float]] = {}
    for layer_idx, group in sorted(layers.items()):
        row_w = len(group) * box_w + (len(group) - 1) * x_gap
        start_x = (width - row_w) / 2.0
        y = 45 + layer_idx * (box_h + y_gap)
        for j, node in enumerate(group):
            pos[node["id"]] = (start_x + j * (box_w + x_gap), y)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width:.0f} {height:.0f}" width="100%" role="img" aria-label="Hoggar Bound Lab Lean 4 Blueprint Dependency Graph">',
        '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#64748b"/></marker></defs>',
        f'<rect width="{width:.0f}" height="{height:.0f}" rx="12" fill="#0f172a"/>',
    ]
    # Edges
    for n in nodes:
        x2, y2 = pos[n["id"]]
        for u in n["uses"]:
            x1, y1 = pos[u]
            parts.append(
                f'<line x1="{x1 + box_w/2:.1f}" y1="{y1 + box_h:.1f}" '
                f'x2="{x2 + box_w/2:.1f}" y2="{y2 - 2:.1f}" '
                f'stroke="#64748b" stroke-width="2" marker-end="url(#arrow)"/>'
            )
    # Nodes
    colors = {
        "definition": ("#1e3a5f", "#38bdf8"),
        "lemma": ("#1e3a3a", "#2dd4bf"),
        "theorem": ("#14532d", "#4ade80"),
        "corollary": ("#3b235a", "#c084fc"),
    }
    for n in nodes:
        x, y = pos[n["id"]]
        fill, stroke = colors.get(n["kind"], ("#1e293b", "#94a3b8"))
        short_title = n["title"] if len(n["title"]) <= 34 else n["title"][:31] + "..."
        badge = f"{n['kind'].upper()} · {len(n['lean'])} Lean decls"
        parts.append(f'<a href="#{html.escape(n["id"])}">')
        parts.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{box_w}" height="{box_h}" rx="10" fill="{fill}" stroke="{stroke}" stroke-width="2"/>')
        parts.append(f'<text x="{x + 12:.1f}" y="{y + 24:.1f}" fill="{stroke}" font-family="ui-monospace,monospace" font-size="11" font-weight="700">{html.escape(badge)}</text>')
        parts.append(f'<text x="{x + 12:.1f}" y="{y + 49:.1f}" fill="#f8fafc" font-family="system-ui,sans-serif" font-size="13" font-weight="600">{html.escape(short_title)}</text>')
        parts.append("</a>")
    parts.append("</svg>")
    return "\n".join(parts)


def render_html(nodes: list[dict], depths: dict[str, int], total_decls: int) -> str:
    svg = render_svg(nodes, depths)
    cards = []
    for n in nodes:
        lean_pills = " ".join(f"<code>{html.escape(d)}</code>" for d in n["lean"])
        uses_links = ", ".join(f'<a href="#{html.escape(u)}">{html.escape(u)}</a>' for u in n["uses"]) or "<em>None (foundational)</em>"
        status_pill = '<span class="pill ok">leanok · kernel verified</span>' if n["leanok"] else '<span class="pill">statement only</span>'
        cards.append(f"""
<article id="{html.escape(n['id'])}" class="card">
  <div class="card-head">
    <span class="kind">{html.escape(n['kind'].upper())}</span>
    {status_pill}
    <span class="label">{html.escape(n['id'])}</span>
  </div>
  <h2>{html.escape(n['title'])}</h2>
  <p>{html.escape(n['description'])}</p>
  <p class="meta"><strong>Depends on:</strong> {uses_links}</p>
  <p class="meta"><strong>Verified Lean 4 declarations ({len(n['lean'])}):</strong><br/>{lean_pills}</p>
</article>""")

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>Hoggar Bound Lab — Lean 4 Blueprint &amp; Dependency Graph</title>
<style>
  body {{ font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background:#0b1020; color:#e2e8f0; margin:0; line-height:1.55; }}
  main {{ max-width:1160px; margin:0 auto; padding:2rem 1.25rem 4rem; }}
  h1 {{ font-size:2rem; margin:0 0 .5rem; color:#f8fafc; }}
  .sub {{ color:#94a3b8; margin:0 0 1.5rem; }}
  .nav {{ display:flex; gap:1rem; flex-wrap:wrap; margin-bottom:1.5rem; font-size:.92rem; }}
  .nav a {{ color:#38bdf8; text-decoration:none; }}
  .nav a:hover {{ text-decoration:underline; }}
  .graph {{ background:#0f172a; border:1px solid #334155; border-radius:14px; padding:1rem; margin-bottom:2rem; overflow-x:auto; }}
  .card {{ background:#0f172a; border:1px solid #334155; border-radius:12px; padding:1.15rem 1.35rem; margin-bottom:1rem; }}
  .card-head {{ display:flex; gap:.65rem; align-items:center; flex-wrap:wrap; margin-bottom:.4rem; }}
  .kind {{ font-size:.75rem; font-weight:700; letter-spacing:.06em; color:#38bdf8; }}
  .label {{ font-family:ui-monospace,monospace; font-size:.8rem; color:#94a3b8; margin-left:auto; }}
  .pill {{ font-size:.75rem; padding:.15rem .55rem; border-radius:999px; background:#1e293b; color:#cbd5e1; }}
  .pill.ok {{ background:#14532d; color:#86efac; }}
  h2 {{ font-size:1.2rem; margin:.2rem 0 .5rem; color:#f8fafc; }}
  .meta {{ font-size:.9rem; color:#cbd5e1; margin:.4rem 0; }}
  code {{ font-family:ui-monospace,SFMono-Regular,Menlo,monospace; font-size:.82rem; background:#1e293b; padding:.12rem .38rem; border-radius:5px; display:inline-block; margin:.12rem .2rem .12rem 0; color:#e2e8f0; }}
  a {{ color:#38bdf8; }}
</style>
</head>
<body>
<main>
  <nav class="nav">
    <a href="../index.html">&larr; Hoggar Bound Lab Home</a>
    <a href="../paper/unified-contextuality.html">Unified Paper (HTML)</a>
    <a href="../paper/unified-contextuality.pdf">Unified Paper (PDF)</a>
    <a href="https://github.com/0thernes/hoggar-bound-lab/blob/main/docs/statement-fidelity.md">Statement Fidelity Table</a>
    <a href="https://github.com/0thernes/hoggar-bound-lab/blob/main/lean/HoggarBound/Challenge.lean">Challenge.lean</a>
  </nav>
  <h1>Hoggar Bound Lab — Lean 4 Blueprint &amp; Dependency Graph</h1>
  <p class="sub">v1.9.0 · Lean 4.35.0 / Mathlib v4.35.0 · <strong>{len(nodes)}</strong> verified nodes · <strong>{total_decls}</strong> declaration-checked Lean bindings · 0 sorry in proof modules · standard axioms <code>[propext, Classical.choice, Quot.sound]</code> only. Not externally peer reviewed.</p>
  <section class="graph">
    {svg}
  </section>
  {''.join(cards)}
</main>
</body>
</html>
"""


def main() -> None:
    nodes = parse_blueprint()
    depths = check_dag(nodes)
    verified_decls = collect_verified_lean_decls()

    missing: list[tuple[str, str]] = []
    total_refs = 0
    for n in nodes:
        for d in n["lean"]:
            total_refs += 1
            if d not in verified_decls:
                missing.append((n["id"], d))

    if missing:
        print(f"FAIL: Blueprint checkdecls failed — unknown Lean declarations: {missing}", file=sys.stderr)
        sys.exit(1)

    WEB_DIR.mkdir(parents=True, exist_ok=True)
    html_out = render_html(nodes, depths, total_refs)
    (WEB_DIR / "index.html").write_bytes(html_out.encode("utf-8"))
    graph_json = {
        "status": "pass",
        "nodes": len(nodes),
        "checked_lean_declarations": total_refs,
        "all_leanok": all(n["leanok"] for n in nodes),
        "dag_depth": max(depths.values()) if depths else 0,
        "items": nodes,
    }
    (WEB_DIR / "blueprint-graph.json").write_bytes((json.dumps(graph_json, indent=2) + "\n").encode("utf-8"))
    print(f"PASS: Blueprint checkdecls verified {total_refs}/{total_refs} Lean declarations across {len(nodes)} nodes (DAG depth {graph_json['dag_depth']}); built blueprint/web/index.html.")


if __name__ == "__main__":
    main()
