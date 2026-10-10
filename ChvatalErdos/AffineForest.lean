import ChvatalErdos.AffineObstruction
import ChvatalErdos.IncidenceForest

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.AffineObstruction

/-- An independent vertex set of H_q gives a forest in its affine incidence graph. -/
theorem graph_independent_forest (q : Nat) [Fact q.Prime]
    (xs : List (Fin (q*q*(q+1))))
    (hi : Independent (graph q) (fun v => v ∈ xs)) :
    OrderedIncidence.IsIncidenceForest (incidence q)
      (xs.map (flagFinEquiv q).symm).toFinset := by
  apply OrderedIncidence.independent_incidence_forest
  intro e he f hf haf
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
  have hxy : x ≠ y := by
    intro h
    subst y
    exact OrderedIncidence.adj_irrefl _ _ haf
  exact hi x y hx hy hxy ⟨haf,OrderedIncidence.adj_symm _ haf⟩

end ChvatalErdos.AffineObstruction

#print axioms ChvatalErdos.AffineObstruction.graph_independent_forest
