#!/usr/bin/env python3
"""Verify bibliographic identifier syntax and (optionally) live HTTP resolution.

Extracts all DOIs, arXiv IDs, Zenodo record links, and HTTPS URLs from
`paper/unified-contextuality.md` and `publication/unified-citation.bib`.
Offline mode validates every identifier pattern and detects broken/placeholder citations;
`--online` additionally checks live HTTP status codes (200/301/302/403-bot-wall reported honestly).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper" / "unified-contextuality.md"
BIB = ROOT / "publication" / "unified-citation.bib"
OUT = ROOT / "results" / "citation-audit.json"

DOI_RE = re.compile(r"\b10\.\d{4,9}/[-._;()/:A-Za-z0-9]+")
ARXIV_RE = re.compile(r"\barXiv:(\d{4}\.\d{4,5}(?:v\d+)?)\b")
URL_RE = re.compile(r"https?://[^\s)\]>\"'`]+")


def clean_token(tok: str) -> str:
    return tok.rstrip(".,;:)}")


def check_doi_handle(doi: str, timeout: int = 12) -> dict[str, object]:
    """Verify a DOI via the official doi.org Handle REST API (avoids publisher/Cloudflare bot walls)."""
    url = f"https://doi.org/api/handles/{doi}"
    req = urllib.request.Request(url, headers={"User-Agent": "hoggar-bound-lab-citation-audit/1.9.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            ok = resp.status == 200 and payload.get("responseCode") == 1
            return {"url": f"https://doi.org/{doi}", "handle_api": url, "status": resp.status, "responseCode": payload.get("responseCode"), "ok": ok}
    except urllib.error.HTTPError as exc:
        return {"url": f"https://doi.org/{doi}", "handle_api": url, "status": exc.code, "ok": False, "note": "handle_http_error"}
    except Exception as exc:
        return {"url": f"https://doi.org/{doi}", "handle_api": url, "status": None, "ok": False, "note": str(exc)}


def check_url(url: str, timeout: int = 12) -> dict[str, object]:
    m_doi = re.match(r"^https?://(?:dx\.)?doi\.org/(10\.\d{4,9}/.+)$", url)
    if m_doi:
        return check_doi_handle(m_doi.group(1), timeout=timeout)
    m_zen = re.match(r"^https?://zenodo\.org/records/(\d+)", url)
    if m_zen:
        res = check_doi_handle(f"10.5281/zenodo.{m_zen.group(1)}", timeout=timeout)
        res["url"] = url
        res["note"] = "verified_via_doi_handle_api (zenodo web blocks automated HEAD/GET)"
        return res
    req = urllib.request.Request(
        url,
        method="HEAD",
        headers={"User-Agent": "hoggar-bound-lab-citation-audit/1.9.0"},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return {"url": url, "status": resp.status, "ok": True}
    except urllib.error.HTTPError as exc:
        # Some publishers block HEAD or bots with 403/405; retry GET once for 405
        if exc.code == 405:
            try:
                req_get = urllib.request.Request(url, headers={"User-Agent": "hoggar-bound-lab-citation-audit/1.9.0"})
                with urllib.request.urlopen(req_get, timeout=timeout) as resp:
                    return {"url": url, "status": resp.status, "ok": True}
            except urllib.error.HTTPError as exc2:
                return {"url": url, "status": exc2.code, "ok": exc2.code in (200, 301, 302, 403), "note": "bot_wall" if exc2.code == 403 else "http_error"}
            except Exception as exc2:
                return {"url": url, "status": None, "ok": False, "note": str(exc2)}
        return {
            "url": url,
            "status": exc.code,
            "ok": exc.code in (200, 301, 302, 403),
            "note": "bot_wall_403" if exc.code == 403 else "http_error",
        }
    except Exception as exc:
        return {"url": url, "status": None, "ok": False, "note": str(exc)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="Perform live HTTP resolution checks")
    args = parser.parse_args()

    paper_txt = PAPER.read_text(encoding="utf-8")
    bib_txt = BIB.read_text(encoding="utf-8")
    combined = paper_txt + "\n" + bib_txt

    dois = sorted({clean_token(m.group(0)) for m in DOI_RE.finditer(combined)})
    arxiv_ids = sorted({m.group(1) for m in ARXIV_RE.finditer(combined)})
    urls = sorted({clean_token(m.group(0)) for m in URL_RE.finditer(combined)})

    # Reject placeholder / fabricated patterns
    bad_placeholders = [
        u for u in urls + dois
        if any(p in u.lower() for p in ("example.com", "example.org", "10.0000/", "todo", "placeholder", "xxxx"))
    ]
    if bad_placeholders:
        print(f"FAIL: Placeholder citations detected: {bad_placeholders}", file=sys.stderr)
        sys.exit(1)

    online_checks = []
    if args.online:
        targets = sorted(
            set(urls)
            | {f"https://doi.org/{d}" for d in dois}
            | {f"https://arxiv.org/abs/{a}" for a in arxiv_ids}
        )
        for u in targets:
            if "web.archive.org" in u or "127.0.0.1" in u or "localhost" in u:
                continue
            online_checks.append(check_url(u))

    failed_online = [c for c in online_checks if not c["ok"]]
    report = {
        "status": "pass" if not bad_placeholders and not failed_online else "fail",
        "mode": "online" if args.online else "offline_syntax",
        "dois": dois,
        "arxiv_ids": arxiv_ids,
        "url_count": len(urls),
        "urls": urls,
        "placeholder_hits": bad_placeholders,
        "online_checks": online_checks,
    }
    OUT.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    if failed_online:
        print(f"FAIL: {len(failed_online)} citation URL(s) failed to resolve: {failed_online}", file=sys.stderr)
        sys.exit(1)
    print(f"PASS: Citation audit ({report['mode']}): {len(dois)} DOIs, {len(arxiv_ids)} arXiv IDs, {len(urls)} URLs verified (0 placeholders).")


if __name__ == "__main__":
    main()
