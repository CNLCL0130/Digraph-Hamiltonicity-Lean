# Verification report

## Archived local verification

The published historical record is in
[verification/verification-status.json](verification/verification-status.json)
and [verification/verification.log](verification/verification.log).
Its final status is `VERIFIED`, with **127 original proof modules** built
from source in the recorded local verification build directory.

| Recorded item | Value |
| --- | --- |
| Final recorded verification | 2026-10-09 15:01:10 UTC (2026-10-09 23:01:10 Asia/Shanghai) |
| Original proof module count | 127 |
| Lean | 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b` |
| mathlib | v4.24.0 |
| Final main theorem audits | Six |
| Permitted and observed axioms | `propext`, `Classical.choice`, `Quot.sound` |

The archive records source SHA-256 hashes, compiled-artifact SHA-256 hashes,
and individual compilation timestamps. The proof source files in
`ChvatalErdos/` and the manuscript source snapshot have retained their exact
bytes from that verified version. Historical `.olean` hashes describe the
original build artifacts; those binary artifacts are not committed.

## Theorem and trust audit

`ChvatalErdos/Main.lean` includes `#print axioms` commands for:

- `ChvatalErdos.main_quantitative`
- `ChvatalErdos.main_asymptotic`
- `ChvatalErdos.main_epsilon`
- `ChvatalErdos.main_linear_lower`
- `ChvatalErdos.main_pancyclic_construction`
- `ChvatalErdos.main_pancyclic_obstruction`

The reported transitive dependencies are limited to Lean/mathlib's standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. No additional
graph-theoretic, extremal, probabilistic, Hamiltonicity, or pancyclicity
conclusion is supplied as a project axiom.

The portable verifier also rejects local occurrences of `sorry`, `admit`,
new `axiom` declarations, `unsafe`, `native_decide`, `implemented_by`, and
`extern` bypasses. Source scanning is supplementary evidence; Lean's
checking and the theorem dependency audits provide the proof verification.
The exact mathematical scope and representations are described in
[PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md).

## Publication additions and privacy editing

The root file `ChvatalErdos.lean` is an additional aggregator importing
`ChvatalErdos.Main` and `ChvatalErdos.AdaptiveOverflow`. It ensures a normal
library build includes every original proof module. It introduces no new
mathematical statement and is not a 128th historically verified proof
module. New verification runs record **127 proof modules plus one root
aggregator** separately.

The published historical metadata and log remove personal absolute machine
paths. The status metadata explicitly marks this redaction, and log source
locations are rendered relative to the repository. Recorded proof hashes,
artifact hashes, timestamps, warnings, and axiom output are preserved.
Consequently the published log and JSON are privacy-edited copies, not
byte-identical copies of the original recording.

The repository also adds portable Lake configuration, a fixed dependency
manifest, a portable verifier, documentation, and manuscript packaging.
None of the 127 original mathematical `.lean` source files was changed.
The supplied PDF is published as a manuscript reference; the archived
verification binds the TeX snapshot, not a freshly compiled PDF.

## Reproduce verification

With Lean/elan, Git, and Python 3.10 or newer installed, run from the
repository root:

```sh
lake exe cache get
python scripts/verify.py
```

The script builds all original local module targets and the root library,
checks the aggregator, rechecks `Main.lean`, and requires the six main axiom
audits to be present and within the permitted set. It rejects source changes
during the run. Current results appear in `.verification/status.json` and
`.verification/verification.log` and are excluded from Git.

For an integrity comparison without a new Lean build:

```sh
python scripts/verify.py --source-only
```

That mode compares all 127 original proof source hashes and the manuscript
source hash with the archived record and scans the additional aggregator.
It does not claim a new proof build. `--skip-build` checks an already
completed local build; its result is labelled `AUDIT_EXISTING_BUILD` and
must not be presented as a fresh complete compilation.

A subsequent GitHub Actions run, when enabled, verifies the repository
revision used by that run. The historical local record and a future CI run
are separate evidence; a future CI result is not implied by this archive.

## Publication-directory Lake verification

The complete Lake build and automatic theorem audit passed at
**2026-10-10T03:30:42.751651+00:00**. The new publication directory contains
127 original proof modules and one additional root aggregator. Its project
build artifacts were generated in this directory; historical project
artifacts were not copied into it. All original proof source bytes match
the author's supplied archive and the archived source hashes.

The six main theorems again report only `propext`, `Classical.choice`, and
`Quot.sound`. The portable verifier also checked the root aggregator and
rechecked the main entry point. The new results are published in
[verification/publication-build-status.json](verification/publication-build-status.json)
and [verification/publication-build.log](verification/publication-build.log).

This local run used the fixed Lean 4.24.0 compiler and the same pinned
dependency versions supplied from a local official cache through Lake
package-path overrides. The missing ProofWidgets JS resources were restored
from its official v0.0.74 release before the successful run. The public
manifest retains ordinary Git dependencies; no local path override is
committed. This is a successful local verification, not a claim that a
GitHub Actions run has already completed.
