"""Check a documentation release against the fixed, verified C3 research artifact.

This checks continuity of the published evidence. It does not rerun the Lean
compiler or establish any claim outside the original theorem statements.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RESEARCH_COMMIT = "d3811e3b53048fa8f3206f08494f0a9834eed287"
SATURATION_COMMIT = "87f08a0fb5007c8529abc13eabeec093027c0eba"
C3_ALL_QUBITS_COMMIT = "5dcea35"  # CarrierFamily.lean as checked by its workflow
VERSION = "1.4.0"
PDF_HASH = "5be6ba1318ce5cfeebf3a89b79dcfd428f87e228234e2f5075b14807a7f34836"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def normalized(data):
    return data.replace(b"\r\n", b"\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="results/publication-v" + VERSION + "-audit.json")
    args = parser.parse_args()
    reference_manifest = json.loads(git("show", RESEARCH_COMMIT + ":results/frontier-c3-lean-source-sha256.json"))
    proof_files = [item["path"] for item in reference_manifest["files"]]
    require(len(proof_files) == 21, "Unexpected reference proof manifest")
    original_files = git("ls-tree", "-r", "--name-only", RESEARCH_COMMIT).decode().splitlines()
    retained = set(proof_files)
    retained.update(name for name in original_files if
                    name.startswith("c3-lab/") or
                    name.startswith("scripts/frontier_c3_") or
                    name.startswith("results/frontier-c3-") or
                    name.startswith("paper/c3-") or
                    name == "tests/frontier_c3_browser_test.cjs")
    retained.update(["LICENSE", "NOTICE"])
    checked = {}
    for name in sorted(retained):
        local = ROOT / name
        require(local.is_file() and not local.is_symlink(), "Missing ordinary artifact: " + name)
        current = local.read_bytes()
        original = git("show", RESEARCH_COMMIT + ":" + name)
        binary = local.suffix in {".pdf", ".png", ".jpg", ".zip"}
        a, b = (current, original) if binary else (normalized(current), normalized(original))
        require(a == b, "Research artifact changed; new verification is needed: " + name)
        checked[name] = {"sha256": sha(a), "normalization": "raw" if binary else "LF"}
    require(sha((ROOT / "paper/c3-spectral-counterexample.pdf").read_bytes()) == PDF_HASH, "Unexpected paper PDF")
    saturation_files = [name for name in git("ls-tree", "-r", "--name-only", SATURATION_COMMIT, "lean").decode().splitlines()
                        if name.endswith((".lean", ".toml", ".json", "lean-toolchain"))]
    saturation_hashes = {}
    for name in saturation_files:
        current = normalized((ROOT / name).read_bytes())
        original = normalized(git("show", SATURATION_COMMIT + ":" + name))
        require(current == original, "Lean source changed since saturation CI: " + name)
        saturation_hashes[name] = sha(current)
    metadata = json.loads((ROOT / "publication/c3-metadata-draft.json").read_text(encoding="utf-8"))
    require(metadata["author_identity_confirmed_by_user"]["given_names"] == "Alexander S.", "Author name mismatch")
    require(metadata["author_identity_confirmed_by_user"]["family_name"] == "Donahue", "Author name mismatch")
    require(metadata["author_identity_confirmed_by_user"]["affiliation_recorded"] == "0thernes LLC", "Affiliation mismatch")
    require(metadata["author_identity_confirmed_by_user"]["orcid"] == "https://orcid.org/0009-0006-8168-9648", "Author-supplied ORCID mismatch")
    require(all(c["affiliation"] == "0thernes LLC" for c in metadata["creators_for_submission"]), "Creator affiliation mismatch")
    require(metadata["arxiv_profile_observed"]["affiliation"] == "0thernes LLC", "Observed arXiv affiliation mismatch")
    require(metadata["version"] == "0.2.0-c3-certificate", "Paper artifact version changed")
    require((ROOT / "VERSION").read_text().strip() == VERSION, "Unexpected documentation version")
    for name in ["GLOSSARY.md", "VERIFICATION.md", "LEGAL.md", "CHANGELOG.md", "docs/RESEARCH-SUMMARY.md", "docs/CLAIMS.md", "docs/research-index.html", "publication/AFFILIATIONS.md"]:
        require((ROOT / name).is_file(), "Missing publication document: " + name)
    axiom_report = json.loads((ROOT / "results/frontier-c3-axioms.json").read_text())
    require(axiom_report["declarations"] == 42 and len(axiom_report["actual"]) == 42, "Unexpected C3 audit size")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(all(set(axioms) <= allowed for axioms in axiom_report["actual"].values()), "Nonstandard axiom in retained report")
    saturation_audit = json.loads((ROOT / "results/saturation-ci-audit.json").read_text())
    require(saturation_audit["checked_commit"] == SATURATION_COMMIT and saturation_audit["workflow_conclusion"] == "success", "Unexpected saturation CI provenance")
    require(saturation_audit["axiom_declarations"] == 14 and len(saturation_audit["actual_axioms"]) == 14, "Unexpected saturation audit size")
    require(all(set(a) <= allowed for a in saturation_audit["actual_axioms"].values()), "Nonstandard saturation axiom")
    # Additions of version 1.3.0: the seven-qubit kernel evaluation and case C3 for every number of qubits.
    seven = json.loads((ROOT / "results/saturation-seven-ci-audit.json").read_text(encoding="utf-8"))
    require(seven["status"] == "pass" and seven["workflow_conclusion"] == "success", "Seven-qubit CI did not pass")
    require(seven["axiom_declarations"] == 13 and len(seven["actual_axioms"]) == 13, "Unexpected seven-qubit audit size")
    require(all(set(a) <= allowed for a in seven["actual_axioms"].values()), "Nonstandard seven-qubit axiom")
    require({"HoggarBound.phase7_degree", "HoggarBound.phase7_contexts"} <= set(seven["actual_axioms"]), "Seven-qubit theorems not audited")
    for name, digest_lf in seven["source_sha256_lf"].items():
        require(sha(normalized((ROOT / name).read_bytes())) == digest_lf, "Source changed since seven-qubit CI: " + name)
    carrier = "lean/HoggarBound/CarrierFamily.lean"
    require(normalized((ROOT / carrier).read_bytes()) == normalized(git("show", C3_ALL_QUBITS_COMMIT + ":" + carrier)),
            "CarrierFamily.lean changed since its checked commit")
    log = (ROOT / "results/lean-c3-all-qubits-axioms.log").read_text(encoding="utf-8")
    reports = {}
    for line in log.splitlines():
        if " depends on axioms: [" in line:
            name, _, axioms = line.partition(" depends on axioms: [")
            reports[name.strip("'")] = {a.strip() for a in axioms.rstrip("]").split(",") if a.strip()}
        elif line.endswith(" does not depend on any axioms"):
            reports[line.split("'")[1]] = set()
    source = (ROOT / carrier).read_text(encoding="utf-8")
    audited = {line.split()[2] for line in source.splitlines() if line.startswith("#print axioms ")}
    require(len(audited) == 74 and audited == set(reports), "C3 all-qubits axiom report does not match the file")
    require(all(a <= allowed for a in reports.values()), "Nonstandard axiom in CarrierFamily.lean")
    require("HoggarBound.C3AllQubits.c3_strict_law_fails_general" in reports, "Main C3 theorem not audited")
    # Addition of version 1.4.0: the exact checks of Lemmas 20 and 21 in the proof of Theorem 19.
    lemma_checks = {}
    for record, total in (("results/conjecture_e_lemmas.json", 115), ("results/conjecture_e_lemmas_n6.json", 46)):
        counts = json.loads((ROOT / record).read_text(encoding="utf-8"))["checks"]
        require(counts == {"passed": total, "total": total}, "Lemma checks incomplete: " + record)
        lemma_checks[record] = counts
    require("conjecture_e_lemmas.py" in (ROOT / ".github/workflows/c3-all-qubits.yml").read_text(encoding="utf-8"),
            "The lemma checks are not a CI step")
    report = {
        "status": "pass",
        "verification_kind": "Documentation-release continuity, not a new Lean compilation",
        "documentation_version": VERSION,
        "research_version": "0.2.0-c3-certificate",
        "research_commit": RESEARCH_COMMIT,
        "paper_pdf_sha256": PDF_HASH,
        "proof_configuration_files_unchanged": len(proof_files),
        "retained_artifacts_checked": len(checked),
        "c3_audited_declarations_in_retained_report": 42,
        "author": "Alexander S. Donahue",
        "affiliation": "0thernes LLC",
        "author_supplied_orcid": "https://orcid.org/0009-0006-8168-9648",
        "license_and_notice_unchanged": True,
        "successful_linux_proof_run": "https://github.com/0thernes/hoggar-bound-lab/actions/runs/42728421086",
        "saturation_ci_commit": SATURATION_COMMIT,
        "saturation_ci_run": "https://github.com/0thernes/hoggar-bound-lab/actions/runs/42741638912",
        "saturation_and_shared_lean_files_unchanged": len(saturation_files),
        "saturation_audited_declarations": 14,
        "saturation_source_lf_sha256": saturation_hashes,
        "seven_qubit_ci_run": seven["run_url"],
        "seven_qubit_audited_declarations": 13,
        "c3_all_qubits_commit": C3_ALL_QUBITS_COMMIT,
        "c3_all_qubits_audited_declarations": len(audited),
        "theorem_19_lemma_checks": lemma_checks,
        "checks": checked,
    }
    output = ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k not in {"checks", "saturation_source_lf_sha256"}}, indent=2))


if __name__ == "__main__":
    main()
