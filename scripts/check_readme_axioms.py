#!/usr/bin/env python3
"""Verify (or update with --write) the verbatim `#print axioms` 5-second proof block in README.md.

Ensures the exact Lean 4 `#print axioms` lines printed in README.md match the recorded
kernel axiom audit logs character-for-character (never paraphrased, never stale).
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"

START_MARKER = "<!-- BEGIN:AXIOMS_5SEC -->"
END_MARKER = "<!-- END:AXIOMS_5SEC -->"

HEADLINE_DECLS = [
    ("results/lean-independent-verification.log", "HoggarBound.hoggar_bound"),
    ("results/lean-independent-verification.log", "HoggarBound.three_qubit_exact_minimum"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.AuditUpgrades.full_space_fraction_tendsto_half"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.hoggar_bound_quaternionic"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.saturation_tfae"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.saturation_mul_isSquare"),
    ("results/lean-saturated-axioms.log", "HoggarBound.pivot_degree"),
    ("results/lean-saturated-axioms.log", "HoggarBound.phase5_degree"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.det6_degree"),
    ("results/lean-saturated-seven-axioms.log", "HoggarBound.phase7_degree"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.NormPhaseFamily.infinite_nonclosed_saturated_family"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.NormPhaseFamily.infinite_nonclosed_family_contextual"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.ExactDegreesN4N5.w72_ge_1455"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.ExactDegreesN4N5.q9plus_ge_6444"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.ExactDegreesN4N5.exact_degrees_n4_n5_of_q7minus_315"),
    ("results/frontier-c3-lean-axioms.log", "HoggarBound.C3.four_qubit_C3_spectral_counterexample"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.C3ExactOptima.corollary16_exact_binary_optima"),
    ("results/lean-c3-all-qubits-axioms.log", "HoggarBound.C3AllQubits.c3_strict_law_fails_general"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.ConjectureE.trace_completion_cube_universal"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.ConjectureE.corollary18_c11_from_c3"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.AuditUpgrades.clifford_transport_strict_law_fails"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.AuditUpgrades.jonah_conjecture_e_all_nine_cases_spectra"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.NonVacuity.conjecture_e_nonvacuous"),
    ("results/new-formalizations-lean-axioms.log", "HoggarBound.NonVacuity.norm_phase_family_nonvacuous"),
]

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def load_axiom_lines(log_rel: str) -> dict[str, str]:
    text = (ROOT / log_rel).read_text(encoding="utf-8")
    flat = re.sub(r"\s+", " ", text)
    out: dict[str, str] = {}
    for name, ax_str in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat):
        axioms = [a.strip() for a in ax_str.split(",") if a.strip()]
        if not set(axioms) <= ALLOWED:
            raise RuntimeError(f"Non-standard axiom in {log_rel} for {name}: {set(axioms) - ALLOWED}")
        out[name] = f"'{name}' depends on axioms: [{', '.join(axioms)}]"
    for name in re.findall(r"'([^']+)' does not depend on any axioms", flat):
        out[name] = f"'{name}' does not depend on any axioms"
    return out


def build_block() -> str:
    cache: dict[str, dict[str, str]] = {}
    lines: list[str] = []
    for log_rel, decl in HEADLINE_DECLS:
        if log_rel not in cache:
            cache[log_rel] = load_axiom_lines(log_rel)
        if decl not in cache[log_rel]:
            raise RuntimeError(f"Missing declaration {decl} in {log_rel}")
        lines.append(cache[log_rel][decl])
    body = "\n".join(lines)
    return f"{START_MARKER}\n```text\n{body}\n```\n{END_MARKER}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Update README.md block in place")
    args = parser.parse_args()

    expected = build_block()
    readme_text = README.read_text(encoding="utf-8").replace("\r\n", "\n")
    pattern = re.compile(re.escape(START_MARKER) + r".*?" + re.escape(END_MARKER), re.S)
    match = pattern.search(readme_text)
    if match is None:
        print(f"FAIL: README.md missing {START_MARKER} ... {END_MARKER}", file=sys.stderr)
        sys.exit(1)

    if args.write:
        updated = pattern.sub(expected, readme_text, count=1)
        README.write_bytes(updated.encode("utf-8"))
        print(f"UPDATED: README.md verbatim #print axioms block ({len(HEADLINE_DECLS)} headline theorems).")
        return

    if match.group(0) != expected:
        print("FAIL: README.md verbatim #print axioms block differs from recorded axiom logs.", file=sys.stderr)
        print("Run: python3 scripts/check_readme_axioms.py --write", file=sys.stderr)
        sys.exit(1)

    print(f"PASS: README.md verbatim #print axioms block matches recorded logs ({len(HEADLINE_DECLS)}/{len(HEADLINE_DECLS)} headline theorems, strictly within {sorted(ALLOWED)}).")


if __name__ == "__main__":
    main()
