# Operations, Backups, and Offsite Preservation (`hoggar-bound-lab`)

`hoggar-bound-lab` is a static research repository with no database or long-running server, so operations focus on **immutable artifact preservation, checksum verification, and offsite repository mirrors** (Build Standard A35).

## Active Preservation Mirrors

1. **Primary Git remote:** `https://github.com/0thernes/hoggar-bound-lab` (tagged releases `v0.1.0` through `v1.9.0`, with `SHA256SUMS` and Sigstore SLSA attestations from `v1.9.0` onward).
2. **Software Heritage (ISO/IEC 18670 SWHID archive):** Independent non-profit archival mirror triggered after every release via the Save Code Now API (e.g. `v1.8.0` snapshot `swh:1:snp:f8afa748054409dffbad57b721d07eb57a545757`).
3. **Master Research Vault (`0thernes-research-archive`):** `https://github.com/0thernes/0thernes-research-archive` pins every release commit as a Git submodule (`repos/hoggar-bound-lab`), stores frozen PDFs and axiom/verifier receipts, and runs daily/push SHA-256 verification via `archive-audit.yml`.
4. **GitHub Pages static mirror:** `https://0thernes.github.io/hoggar-bound-lab/` serves the unified paper PDF/HTML, interactive explorers (`c3-lab/`, `independent-review/`), and the Lean Blueprint (`/blueprint/`), assembled from a single workflow (`.github/workflows/independent-pages.yml`).

## Creating an Offline Git Bundle & Offsite Mirror

```bash
# Create a self-contained verifiable git bundle backup of all branches and tags
git bundle create ../hoggar-bound-lab-backup-$(date +%F).bundle --all
git bundle verify ../hoggar-bound-lab-backup-$(date +%F).bundle

# Mirror-push to a secondary offsite remote named `backup`
git remote add backup <OFFSITE_REMOTE_URL>
git push backup --mirror
```

## Restoring & Verifying From Backup

```bash
git clone hoggar-bound-lab-backup-YYYY-MM-DD.bundle hoggar-bound-lab-restored
cd hoggar-bound-lab-restored
(cd data && sha256sum -c MANIFEST.sha256)
python3 scripts/publication_release_audit.py
python3 scripts/unified_publication_audit.py
```
