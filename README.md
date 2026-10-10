# Lean formalization of “A near-linear Chvátal–Erdős condition for Hamilton cycles in digraphs”

This project formalizes the manuscript by **Chengli Li and Bo Ning** using
Lean 4 with mathlib. It includes the [manuscript PDF](manuscript/paper.pdf)
and the [LaTeX source snapshot](manuscript/paper.tex) used for the
formalization.

PDF SHA-256: `aacbbdf1de06f3dc3ed5c612328210c8a2019053522357b57286fea6cae3efa9`.
TeX SHA-256: `39995ece3895bb93781f334d4e2511f0d2cafebd4e680010f42041246811f8bb`.

The repository contains **127 original proof modules and one root library
entry point**. A complete local Lake source build and the six main theorem
dependency audits passed on **10 October 2026 at 03:30 UTC**. The earlier
complete local verification of the 127 original modules is also archived.
See [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md) for the actual check
status, source provenance, and dependency-cache details.

The detailed manuscript correspondence is
[PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md). The original proof source bytes are
preserved from the verified archive; [SHA256SUMS](SHA256SUMS) records the
integrity hashes of the packaged files.

## Entry points

- [ChvatalErdos.lean](ChvatalErdos.lean): the library root, importing `Main`
  and `AdaptiveOverflow` to include all 127 original proof modules.
- [ChvatalErdos/Main.lean](ChvatalErdos/Main.lean): the six main manuscript
  conclusions, compatibility checks for the quantitative and asymptotic
  claim statements, and their `#print axioms` audits.
- [ChvatalErdos/AdaptiveOverflow.lean](ChvatalErdos/AdaptiveOverflow.lean):
  the auxiliary adaptive Laplace-transform and Chernoff estimates,
  `FiniteProbability.adaptive_laplace_power` and
  `FiniteProbability.adaptive_chernoff`.

Each entry point imports the focused source modules containing its proofs.
`lake build` checks the complete library; `lake env lean
ChvatalErdos/Main.lean` rechecks the main statements and prints their
transitive axiom dependencies.

## Current verified layer

- `Core.lean`, `Connectivity.lean`, and `InducedCore.lean`: finite digraphs,
  2-cycle independence, strong connectivity under vertex deletion,
  induced graphs, minimum degree, and actual Hamilton cycles. The central
  definitions are `Digraph`, `AlphaTwoLE`, `KStrong`, and `Hamiltonian`.
- `PancyclicDefinitions.lean`: actual directed cycle lengths, pancyclicity,
  triangle freeness, the independence number `alpha₂`, and vertex
  connectivity `connectivity` (alias `κ`), including their equivalence
  with the bound and strong-connectivity predicates.
- `LeastBound.lean`: existence and minimality of the positive sufficient
  connectivity threshold `f₂`, through `sufficient_exists`,
  `f₂_sufficient`, `f₂_pos`, and `f₂_le`.
- `CaroWei.lean`: the random-order proof of `caro_wei` and its density
  consequence. `FourCycle.lean`, `PikhurkoDegree.lean`,
  `PikhurkoGrowth.lean`, and the supporting degree, bipartite, chord, and
  level modules prove the even-cycle extremal bound exposed as
  `even_cycle_degree_bound` in `EvenCycleBound.lean`.
- `Remainder.lean` and `ExtremalReduction.lean`: the maximal-remainder
  estimate. `Forest.lean`, `CutMatching.lean`, and
  `InducedCutMatching.lean`: forest extension, path covers, endpoint
  counts, partial Hall matchings, and cut matchings after vertex deletion.
- `FiniteProbability.lean`, `Chernoff.lean`, and
  `NegativeAssociation.lean`: finite uniform product probability,
  Markov's inequality, Laplace-transform lower tails, and the required
  negative-correlation properties. `DeferredDecisions.lean`,
  `AdaptiveQueries.lean`, `ConditionalFreeze.lean`, and
  `AdaptiveOverflow.lean` establish the adaptive exposure estimates from
  complete query histories.
- `MatchingSurvival.lean`, `GlobalNeighbours.lean`,
  `WeightedFailure.lean`, and `Estimates.lean`: matching survival,
  distinct-part properties, simultaneous neighbour bounds, and the
  degree-weighted numerical estimates. The matching argument allows
  several original matching edges to belong to the same part.
- `RecordAlgorithm.lean`, `RecordInvariants.lean`,
  `RecordSeparations.lean`, `RecordWords.lean`, `FreshLaplace.lean`,
  `RecordOverflow.lean`, `NormalStopBound.lean`, and
  `RecordProbability.lean`: compatible separation records, their
  invariants, overflow and normal stopping bounds, and the union over
  records and colours. `Selection.lean` and `CoreSelection.lean` prove
  `selection_exists` and `core_selection_exists`, including prescribed
  endpoints.
- `LinkageHall.lean`, `LinkagePaths.lean`, `PathExpansion.lean`,
  `InitialForest.lean`, `HalvingMerge.lean`, and the `Layer` modules:
  set linkage, initial path forests, and iterative path merging.
  `CycleInsertion.lean`, `CycleInsertionLinks.lean`,
  `BidirectionalInsertion.lean`, `ForestHamiltonian.lean`,
  `CycleCoreHamiltonian.lean`, and `PackingHamiltonian.lean` complete
  the insertion and Hamilton-cycle construction.
- `Budgets.lean`, `LogBudgets.lean`, `RemainderLogBound.lean`,
  `AsymptoticLarge.lean`, `AsymptoticFinite.lean`, and
  `EpsilonBound.lean`: the explicit budgets, asymptotic parameter choice,
  rounding, finite small parameters, and the bound with every positive
  exponent increment. `BipartiteExample.lean` and
  `LinearLowerBound.lean` prove the complete bipartite obstruction and
  `f₂_linear_lower`.
- `OrderedIncidence.lean`, `AffineObstruction.lean`,
  `AffineBaseProperties.lean`, `IncidenceForest.lean`, and
  `AffineForest.lean`: the affine incidence structure, point/line/flag
  counts, degrees, uniqueness of the line through two points, absence
  of incidence four-cycles, the independent-incidence forest assertion,
  triangle freeness, and the independence bound.
- `FourPartObstruction.lean`, `ObstructionEstimates.lean`, and
  `PancyclicObstruction.lean`: the four-part Hamiltonian construction,
  its exact connectivity, independence bound and triangle freeness,
  arbitrarily large prime parameters, and the resulting pancyclicity
  counterexamples. These include `pancyclic_construction`,
  `pancyclic_obstruction`, and
  `jackson_ordaz_pancyclic_counterexample`.

## Main theorem and manuscript map

Here `α₂(D)` is the largest size of a vertex set containing no directed
2-cycle, `κ(D)` is vertex connectivity, and `f₂(a)` is the least positive
connectivity threshold sufficient for Hamiltonicity when `α₂(D) ≤ a`.
All theorem names below are in the `ChvatalErdos` namespace.

| Manuscript statement | Lean theorem | Verified conclusion |
| --- | --- | --- |
| `thm:quantitative` | `main_quantitative` | `f₂(a) ≤ remainderBudget a k + connectionBudget a k` for integers `a ≥ 2`, `k ≥ 2`, `3 ∤ k` |
| `thm:asymptotic` | `main_asymptotic` | Some uniform `C > 0` gives `f₂(a) ≤ C a(log a)⁴/(log log a)²` for every integer `a ≥ 3` |
| `cor:epsilon` | `main_epsilon` | For every real `ε > 0`, some `C > 0` gives `f₂(a) ≤ C a^(1+ε)` for every integer `a ≥ 3` |
| Introductory complete bipartite lower bound | `main_linear_lower` | `a ≤ f₂(a)` for every integer `a ≥ 2` |
| `thm:pancyclic-construction` | `main_pancyclic_construction` | For every prime `q ≥ 11`, a Hamiltonian digraph of order `4q²(q+1)` with `κ = q²(q+1)`, `α₂ ≤ 8q²+4q−4`, no directed triangle, non-pancyclicity, and `α₂+1 ≤ κ` |
| `thm:pancyclic-obstruction` | `main_pancyclic_obstruction` | No positive constant `c` makes `κ(D) ≥ c α₂(D)` sufficient for pancyclicity of every Hamiltonian digraph |

The complete correspondence, intermediate lemmas, numerical conventions,
and equivalent mathematical reconstructions are documented in
[PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md).

## Build

With [elan](https://lean-lang.org/install/)/Lake and Git installed, run
from the repository root:

```sh
lake exe cache get
lake build
lake env lean ChvatalErdos/Main.lean
```

The project pins Lean **4.24.0** in `lean-toolchain` and mathlib
**v4.24.0** in `lakefile.toml`; `lake-manifest.json` fixes all dependency
commits. Dependency caches supply mathlib build files; the local proof
modules are compiled from source.

With Python 3.10 or newer, the portable verifier builds every local proof
module and the root aggregator, then audits all six main theorem
dependencies:

```sh
python scripts/verify.py
```

Its current results are saved in `.verification/`, excluded from Git.
`python scripts/verify.py --source-only` instead compares the original
proof sources and TeX snapshot with the archived hashes; it is an integrity
check and does not run a new Lean build.

The [GitHub Actions workflow](.github/workflows/lean.yml) is configured to
check packaged hashes, compare source integrity, obtain the official
dependency cache, compile all local proof modules, and audit the six main
theorems. Run results are available on the
[Actions page](https://github.com/CNLCL0130/Digraph-Hamiltonicity-Lean/actions).
The completed local Lake build is recorded separately in
[publication-build-status.json](verification/publication-build-status.json)
and [publication-build.log](verification/publication-build.log).

## Scope and trust

The verified targets are the manuscript's six main research conclusions
and the definitions, constructions, and lemmas needed to prove them.
Historical theorems and conjectures appearing in the literature review
are not independent targets. The required Caro–Wei and even-cycle
extremal estimates are proved in this project; the main results do not
take additional literature conclusions as premises.

There are no project `sorry`, `admit`, or new `axiom` declarations.
The transitive audits of all six main theorems report only `propext`,
`Classical.choice`, and `Quot.sound`, the standard axioms used by
Lean/mathlib. The verifier additionally rejects project uses of `unsafe`,
`native_decide`, `implemented_by`, and `extern` bypasses.

The complete local source build of the original 127 modules on
**9 October 2026** and the complete publication-directory Lake build of
**127 proof modules plus one root aggregator on 10 October 2026** are
separate recorded checks. Published logs remove personal absolute machine
paths while preserving theorem audit output and source hashes.
See [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md) for their evidence,
the mathematical scope, and the reproduction procedure. Any later CI run
provides verification evidence for its own checked-out revision.
