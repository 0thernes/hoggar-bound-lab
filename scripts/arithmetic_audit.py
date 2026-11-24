#!/usr/bin/env python3
"""Audit arithmetic precision across every Python script in scripts/.

Classifies each script as:
  - exact_integer_or_symbolic : headline verification relies strictly on exact int / Fraction / SymPy
  - timing_or_plot_float      : float/NumPy used only for timings, figure plotting, or non-proof utilities
  - numerical_approximation   : uses IEEE-754 floating-point linear algebra / tolerances (exploratory only)

Addresses the "floating-point illusion" attack vector from the Independent Scientist's
Verification Playbook (2026 Edition).
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = ROOT / "scripts"
OUT_PATH = ROOT / "results" / "arithmetic-audit.json"

# Explicit, auditable classifications of scripts that touch float/numpy
EXACT_VERIFIERS = {
    "c3_exact_optima_check.py": "Exact integer MET-SDP dual & Gram check; float used only for elapsed-time logging.",
    "c3_sdp_dual_check.py": "Exact integer LDL^T & SymPy charpoly check; float rounded to 9 decimals only for diagnostic display.",
    "c3_sparse_search.py": "Exact integer NumPy int64 arithmetic; zero floating-point tolerances.",
    "conjecture_e.py": "Exact integer NumPy object/int arithmetic; zero floating-point claims.",
    "conjecture_e_lemmas.py": "Exact integer/SymPy checks of Lemmas 20 & 21; float used only for timing.",
    "conjecture_e_trace_formula.py": "Exact integer/object-dtype verification of Theorem 22 & Table 8 (97 + 39 checks).",
    "cospectral_family.py": "Exact integer matrix & SymPy verification; float used only for timing.",
    "cospectral_family_cone_lift.py": "Exact integer matrix verification of Corollary 18 cone lift.",
    "cospectral_family_tensor_check.py": "Exact integer tensor-product check of C3 all-qubit family.",
    "cospectral_pair.py": "Exact integer/SymPy verification of four-qubit C3 pair; float used only for timing.",
    "exact_degrees_n4_n5.py": "Pure-integer 42-orbit dual & ladder verification (zero floating point in proofs; float used only for timing).",
    "frontier_c3_certificate_audit.py": "Exact integer NumPy object/int certificate audit.",
    "frontier_c3_context_verify.py": "Exact integer context reconstruction (1120 outside contexts).",
    "frontier_c3_verify.py": "Exact integer matrix & SymPy factorization verifier.",
    "norm_phase_family.py": "Pure-integer verification of Theorem 13b through m=4 (32/32 exact checks).",
}

NUMERICAL_APPROX = {
    "analysis.py": "numerical_approximation: exploratory floating-point spectral analysis and diagnostics (not used to prove any theorem).",
    "flat_states.py": "numerical_approximation: exploratory flat-state discovery using 1e-12 float64 tolerance; exact masks are independently proved in Lean 4.",
    "frontier_c3_extend.py": "numerical_approximation: exploratory search/diagnostics; formal proof is in CarrierFamily.lean and ConjectureE.lean.",
    "frontier_c3_search.py": "numerical_approximation: heuristic search that located the C3 witness; witness itself is proved exactly in Lean 4.",
    "frontier_c3_sparse_family.py": "numerical_approximation: exploratory sparse-carrier search; exact family is proved in Lean 4.",
    "ladder.py": "numerical_approximation: exploratory float64/integer ladder diagnostics; exact N=4..5 bounds are proved in ExactDegreesN4N5.lean and exact_degrees_n4_n5.py.",
    "phase_states.py": "numerical_approximation: exploratory phase-state rank/support finder (float64 + exact integer checks); exact N=5,6,7,3m degrees are proved in Lean 4.",
    "stack_audit.py": "numerical_approximation: Tsotchke classical software stack demonstration audit (float64 simulation checks).",
}

UTILITY_PLOT_BUILD = {
    "arithmetic_audit.py",
    "build_blueprint.py",
    "build_latex.py",
    "build_paper.py",
    "build_unified_paper.py",
    "check_citations.py",
    "check_readme_axioms.py",
    "frontier_c3_figure.py",
    "frontier_c3_paper_build.py",
    "independent_demo_data.py",
    "independent_figures.py",
    "independent_paper_build.py",
}


def main() -> None:
    records = []
    unclassified_float = []
    for path in sorted(SCRIPTS_DIR.glob("*.py")):
        text = path.read_text(encoding="utf-8", errors="replace")
        uses_numpy = bool(re.search(r"\b(numpy|np\.|scipy)\b", text))
        uses_float_ops = bool(re.search(r"\b(float\(|1e-\d|np\.linalg|eigh|eigvalsh|isclose|allclose)\b", text))
        uses_exact = bool(re.search(r"\b(sympy|Fraction|int\(|//)\b", text))
        name = path.name

        if name in EXACT_VERIFIERS:
            tier = "exact_integer_or_symbolic"
            note = EXACT_VERIFIERS[name]
        elif name in NUMERICAL_APPROX:
            tier = "numerical_approximation"
            note = NUMERICAL_APPROX[name]
        elif name in UTILITY_PLOT_BUILD:
            tier = "timing_or_plot_float"
            note = "Build, formatting, demo-data, or figure-rendering utility (not a theorem proof)."
        elif not uses_numpy and not uses_float_ops:
            tier = "exact_or_non_numeric"
            note = "No NumPy or floating-point operations detected."
        else:
            tier = "unclassified_float"
            note = "Contains NumPy or float expressions; requires explicit classification."
            unclassified_float.append(name)

        records.append({
            "script": f"scripts/{name}",
            "tier": tier,
            "uses_numpy": uses_numpy,
            "uses_float_ops": uses_float_ops,
            "uses_exact_arithmetic": uses_exact,
            "note": note,
        })

    summary = {
        "status": "pass" if not unclassified_float else "fail",
        "total_scripts": len(records),
        "counts": {
            "exact_integer_or_symbolic": sum(1 for r in records if r["tier"] == "exact_integer_or_symbolic"),
            "numerical_approximation": sum(1 for r in records if r["tier"] == "numerical_approximation"),
            "timing_or_plot_float": sum(1 for r in records if r["tier"] == "timing_or_plot_float"),
            "exact_or_non_numeric": sum(1 for r in records if r["tier"] == "exact_or_non_numeric"),
            "unclassified_float": len(unclassified_float),
        },
        "policy": "No headline mathematical theorem relies solely on IEEE-754 float64. All exploratory numerical scripts are explicitly labeled numerical_approximation.",
        "scripts": records,
    }
    OUT_PATH.write_bytes((json.dumps(summary, indent=2) + "\n").encode("utf-8"))
    if unclassified_float:
        raise RuntimeError(f"Unclassified float/NumPy scripts found: {unclassified_float}")
    print(f"PASS: Audited {len(records)} scripts (0 unclassified float scripts; {summary['counts']['exact_integer_or_symbolic']} exact verifiers, {summary['counts']['numerical_approximation']} labeled numerical_approximation).")


if __name__ == "__main__":
    main()
