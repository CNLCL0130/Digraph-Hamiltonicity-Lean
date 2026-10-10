# Manuscript-to-Lean correspondence

This map describes the proof structure for the source snapshot
[manuscript/paper.tex](manuscript/paper.tex). It is based on the original
detailed [proof-map.txt](proof-map.txt), preserved alongside this English
guide. Verification evidence is recorded separately in
[VERIFICATION_REPORT.md](VERIFICATION_REPORT.md).

Unless qualified otherwise, theorem names below are in the `ChvatalErdos`
namespace. The library entry point is [ChvatalErdos.lean](ChvatalErdos.lean);
the six principal statements are in [Main.lean](ChvatalErdos/Main.lean).

## Main statements

| Manuscript statement or label | Lean statement | Meaning |
| --- | --- | --- |
| `thm:quantitative` | `main_quantitative` | `f₂(a) ≤ remainderBudget a k + connectionBudget a k` for `a ≥ 2`, `k ≥ 2`, `3 ∤ k` |
| `thm:asymptotic` | `main_asymptotic` | A uniform positive constant bounds `f₂(a)` by `C a(log a)⁴/(log log a)²` for all `a ≥ 3` |
| `cor:epsilon` | `main_epsilon` | For each `ε > 0`, a uniform positive constant bounds `f₂(a)` by `C a^(1+ε)` for all `a ≥ 3` |
| Introductory complete bipartite lower bound | `main_linear_lower` | `a ≤ f₂(a)` for all `a ≥ 2` |
| `thm:pancyclic-construction` | `main_pancyclic_construction` | The prime-parameter Hamiltonian construction, exact connectivity, independence bound, triangle freeness, non-pancyclicity, and `α₂+1 ≤ κ` |
| `thm:pancyclic-obstruction` | `main_pancyclic_obstruction` | No positive linear connectivity constant guarantees pancyclicity |

[LeastBound.lean](ChvatalErdos/LeastBound.lean) proves the existence and
minimality of the sufficient threshold through `sufficient_exists`,
`f₂_sufficient`, `f₂_pos`, and `f₂_le`. The definition of `f₂` uses `Nat.find`
after existence has been proved. `Main.lean` also checks the corresponding
`QuantitativeClaim`, `AsymptoticClaim`, and `EpsilonClaim` statements.

## Hamiltonicity upper bound

| Manuscript component | Principal Lean files and statements |
| --- | --- |
| Digraphs, 2-cycle independence, strong connectivity, Hamilton cycles | `Core.lean`: `Digraph`, `AlphaTwoLE`, `KStrong`, `Hamiltonian` |
| Minimum degree, vertex deletion, induced graphs | `Connectivity.lean`, `InducedCore.lean` |
| `thm:carowei` | `CaroWei.lean`: `caro_wei`, `caro_wei_density`, using a random vertex order |
| `thm:pikhurko` | `EvenCycleBound.lean`: `even_cycle_degree_bound`; `FourCycle.lean` handles `k = 2`; `DegreeCore.lean`, `BipartiteCut.lean`, `ChordedDensity.lean`, `ChordPathLemma.lean`, `RootedParent.lean`, `AncestorSplit.lean`, `LevelChordCycle.lean`, `LevelBounds.lean`, `PikhurkoDegree.lean`, and `PikhurkoGrowth.lean` give the general bound |
| `lem:remainder` | `Remainder.lean`: `remainder_from_degree_bound`; `ExtremalReduction.lean`: `maximal_remainder_bound` |
| `lem:forest` | `Forest.lean`: `Forest.extension`, `Forest.path_cover`, `Forest.ends_card_le` |
| `lem:cutmatching` | `CutMatching.lean`: `partial_hall`, `cut_matching`; `InducedCutMatching.lean` handles induced graphs after deletion |
| Independent and negatively correlated Bernoulli lower tails | `Chernoff.lean`, `NegativeAssociation.lean`: Laplace transforms, Markov's inequality, negative-correlation closure, exponential estimates |
| `lem:part-selection` | `MatchingSurvival.lean`: `FiniteProbability.PartSelection.matching_survival_tail` and the distinct-part properties of surviving matching edges |
| Finite selection and deferred exposure | `FiniteProbability.lean`, `DeferredDecisions.lean`, `AdaptiveQueries.lean`, `ConditionalFreeze.lean` |
| `cl:neighbours` | `GlobalNeighbours.lean`: `all_neighbour_failure_bound`; `WeightedFailure.lean`, `Estimates.lean` |
| `cl:effective` | `CycleEndpoints.lean`: `mixed_cycle_has_effective_pair`; `RecordSeparations.lean` |
| `cl:records` | `RecordAlgorithm.lean`, `RecordInvariants.lean`, `RecordWords.lean`: `Record.Separation.exists_compatible_record` |
| `cl:overflow` | `AdaptiveOverflow.lean`, `FreshLaplace.lean`, `RecordOverflow.lean`: `Record.overflow_selection_budget` |
| `cl:stopped` | `NormalRecords.lean`, `SmallSide.lean`, `LargeSide.lean`, `NormalStopBound.lean`: `Record.normal_stopping_bound` |
| Union over records and colours | `RecordProbability.lean`: `Record.all_separations_probability` |
| `lem:selection` | `Selection.lean`: `selection_exists`; `CoreSelection.lean`: `core_selection_exists`, including prescribed endpoints |
| `lem:linkage` | `LinkageHall.lean`, `OrbitSegments.lean`, `LinkagePaths.lean`, `PathExpansion.lean` |
| `cl:initial` | `InitialForest.lean`: `initial_forest` |
| `cl:merging` and iterative halving | `HalfIndices.lean`, `HalvingMerge.lean`, `LayerMerge.lean`, `LayerIteration.lean`, `LayerCycle.lean` |
| `cl:extension` and final insertion | `CycleInsertion.lean`, `CycleInsertionLinks.lean`, `BidirectionalInsertion.lean` |
| Assembly into a Hamilton cycle | `ForestHamiltonian.lean`, `CycleCoreHamiltonian.lean`, `PackingHamiltonian.lean`, `ExtremalReduction.lean` |
| Asymptotic parameter selection, rounding, finite small parameters | `LogBudgets.lean`, `RemainderLogBound.lean`, `AsymptoticLarge.lean`, `AsymptoticFinite.lean` |
| The `ε` corollary | `EpsilonBound.lean`: `scale_power_bound`, `epsilon_claim` |
| Complete bipartite lower bound | `BipartiteExample.lean`, `LinearLowerBound.lean`: `unbalanced_counterexample`, `f₂_linear_lower` |
| Numerical budgets | `Budgets.lean`, `Estimates.lean`, `Selection.lean`, `NormalStopBound.lean`, `RecordProbability.lean` |

The Caro–Wei and required even-cycle extremal bounds are proved within the
project; they are not assumed as extra graph-theoretic axioms. The matching
and set-linkage arguments use Hall's theorem to establish the needed
conclusions, without taking general König or Menger statements as additional
premises. The part-selection proof permits multiple original matching edges
in one part. Independence of unexposed coordinates is derived from complete
query histories.

## Pancyclicity obstruction

| Manuscript component | Principal Lean files and statements |
| --- | --- |
| Actual cycle lengths, pancyclicity, triangle freeness | `PancyclicDefinitions.lean`: `HasCycleLength`, `Pancyclic`, `TriangleFree`, `triangleFree_not_hasCycleLength_three`, `triangleFree_not_pancyclic` |
| Actual independence number and vertex connectivity | `PancyclicDefinitions.lean`: `alpha₂`, `connectivity` (alias `κ`), `alphaTwoLE_iff_alpha₂_le`, `kStrong_iff_le_connectivity`, and the zero-value conventions |
| Affine incidence and flag counts | `AffineObstruction.lean`: `AffineObstruction.incidence`, `flag_card`, `line_card`, `no_four` |
| `lem:affine-base-properties` | `AffineBaseProperties.lean`: `point_card`, `point_degree`, `line_degree`, `common_line_exists`, `unique_common_line`, `base_properties`, `pointNeighborsEquiv`, `lineNeighborsEquiv` in `AffineObstruction` |
| `lem:affine-triangle-free` | `OrderedIncidence.lean`: `OrderedIncidence.triangle_impossible`; `AffineObstruction.lean`: `AffineObstruction.graph_triangleFree` |
| Forest assertion in `lem:affine-independence` | `IncidenceForest.lean`: `OrderedIncidence.SelectedIncidence`, `IsIncidenceForest`, `independent_incidence_forest`; `AffineForest.lean`: `AffineObstruction.graph_independent_forest` |
| Independence bound in `lem:affine-independence` | `OrderedIncidence.lean`: `OrderedIncidence.independent_card_bound`; `AffineObstruction.lean`: `AffineObstruction.graph_alphaTwoLE` |
| Cyclic connection of four copies | `FourPartObstruction.lean`: `fourPartDigraph`, `fourPart_hamiltonian`, `fourPart_kStrong`, `fourPart_not_kStrong_succ`, `fourPart_connectivity`, `fourPart_alpha`, `fourPart_triangleFree`, `fourPart_properties` |
| Full prime-parameter construction | `PancyclicObstruction.lean`: `pancyclicExample`, `pancyclic_construction` |
| Arbitrarily large primes and ratio estimates | `ObstructionEstimates.lean`: `obstruction_prime_exists`, `obstruction_ratio_bound`, `obstruction_conjecture_bound` |
| No fixed linear pancyclicity condition | `PancyclicObstruction.lean`: `pancyclic_counterexample`, `pancyclic_obstruction` |
| The stated Jackson–Ordaz pancyclicity counterexample | `PancyclicObstruction.lean`: `jackson_ordaz_pancyclic_counterexample` |

The affine base has `q²` points, `q(q+1)` lines, and `q²(q+1)` flags; point
and line degrees are `q+1` and `q`. Distinct points determine exactly one
line. `IsIncidenceForest` excludes all simple alternating cycles of length
`2k`, `k ≥ 2`, requiring injective vertex sequences on both sides and all
successive and closing incidence edges. The independent vertices of the
constructed graph are mapped back to flags.

The numerical bound has a direct injection proof into the union of points
and lines, with at least one unused line, yielding `|I| ≤ |U|+|W|−1`.
Both the forest assertion and the numerical bound are proved. Connectivity
of the four-part construction is an equality: deleting one part gives the
upper bound; every deletion of fewer vertices gives the lower bound.

## Representation and scope

- Finite digraphs use `Fin n` as their vertex type. Opposite arcs are allowed,
  loops are excluded, and 2-cycle independence concerns pairs of opposite
  arcs rather than the absence of every arc.
- `Hamiltonian` includes order at least two, a bijective vertex enumeration,
  consecutive arcs, and the closing arc. `HasCycleLength` uses actual
  injective cyclic enumerations. `Pancyclic` requires every length from
  two through the graph order.
- `colourCount a = Nat.clog 2 a + 1`; other logarithms are `Real.log`.
  The rounded remainder expression is positive in the theorem's range.
  `connectionBudget = 2¹⁶(2k)²a·colourCount(a)²` equals the manuscript's
  `2¹⁸k²aℓ²`.
- The probability spaces are the finite uniform product spaces used in the
  proof. Adaptive lower-tail estimates use conditional success-probability
  bounds derived from the query history.
- Affine points use the standard correspondence between finite indices and
  `ZMod q × ZMod q`: `q·x+y` corresponds to `(x,y)`, preserving the stated
  lexicographic order. General ordered-incidence results are applied to
  this concrete construction.
- The asymptotic proof establishes a uniform inequality for all `a ≥ 3`.
  It does not separately formalize every intermediate `O`, `o`, or `∼`
  expression or optimize constants.
- The targets are the manuscript's research conclusions and the lemmas
  needed for them. Literature-review statements and historical conjectures
  are not independent targets.
