import ChvatalErdos.OrderedIncidence

/-!
The forest assertion in the affine construction: independent vertices of the
ordered superline graph correspond to an acyclic bipartite incidence graph.

A simple bipartite cycle has even length `2*k`, with `k ≥ 2`, and can be
enumerated by distinct vertices on each side in alternating cyclic order.
`IsIncidenceForest` excludes precisely these simple alternating cycles.
-/

set_option autoImplicit false

namespace ChvatalErdos.OrderedIncidence

variable {U W : Type} [LinearOrder U]

/-- The selected incidence graph has this edge. -/
def SelectedIncidence (inc : U → W → Prop) (s : Finset (Flag inc))
    (u : U) (w : W) : Prop :=
  ∃ e : Flag inc, e ∈ s ∧ e.val.1 = u ∧ e.val.2 = w

/-- The selected bipartite graph contains no simple alternating cycle.
The two injectivity conditions express simplicity on the two disjoint sides;
the edges incident with `w i` join `u i` and `u (cyclicSucc i)`. -/
def IsIncidenceForest (inc : U → W → Prop) (s : Finset (Flag inc)) : Prop :=
  ∀ (k : Nat), 2 ≤ k → ∀ (u : Fin k → U) (w : Fin k → W),
    Function.Injective u → Function.Injective w →
    (∀ i, SelectedIncidence inc s (u i) (w i) ∧
      SelectedIncidence inc s (u (cyclicSucc i)) (w i)) → False

private def incidencePred {k : Nat} (i : Fin k) : Fin k :=
  if hi : i.val = 0 then ⟨k-1, by have h := i.isLt; omega⟩
  else ⟨i.val-1, by have h := i.isLt; omega⟩

private theorem incidencePred_succ {k : Nat} (i : Fin k) :
    cyclicSucc (incidencePred i) = i := by
  apply Fin.ext
  by_cases hi : i.val = 0
  · have hk := i.isLt
    simp only [incidencePred, dif_pos hi, cyclicSucc]
    have hsub : k-1+1 = k := by omega
    rw [hsub,Nat.mod_self,hi]
  · have hk := i.isLt
    simp only [incidencePred, dif_neg hi, cyclicSucc]
    have hsub : i.val-1+1 = i.val := by omega
    rw [hsub,Nat.mod_eq_of_lt hk]

private theorem incidencePred_ne {k : Nat} (hk : 2 ≤ k) (i : Fin k) :
    incidencePred i ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  by_cases hi : i.val = 0
  · simp only [incidencePred,dif_pos hi] at hv
    omega
  · simp only [incidencePred,dif_neg hi] at hv
    omega

/-- An independent set in the ordered incidence graph selects a forest in
the original bipartite graph. This does not require the no-four-cycle property. -/
theorem independent_incidence_forest (inc : U → W → Prop) (s : Finset (Flag inc))
    (hs : ∀ e ∈ s, ∀ f ∈ s, ¬ Adj inc e f) : IsIncidenceForest inc s := by
  classical
  intro k hk u w hu hw hcycle
  let active : Finset U := Finset.univ.image u
  have ha : active.Nonempty := by
    exact ⟨u ⟨0,by omega⟩,Finset.mem_image.mpr ⟨⟨0,by omega⟩,Finset.mem_univ _,rfl⟩⟩
  let smallest := active.min' ha
  have hsmall : smallest ∈ active := Finset.min'_mem _ _
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hsmall
  have hmin : ∀ i : Fin k, u j ≤ u i := by
    intro i
    rw [hj]
    exact Finset.min'_le active (u i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let p := incidencePred j
  have hpj : p ≠ j := incidencePred_ne hk j
  have hjp : j ≠ p := hpj.symm
  have hlt : u j < u p := lt_of_le_of_ne (hmin p) (fun h => hjp (hu h))
  have hwp : w j ≠ w p := fun h => hjp (hw h)
  obtain ⟨e,he,heu,hew⟩ := (hcycle j).1
  obtain ⟨f,hf,hfu,hfw⟩ := (hcycle p).1
  obtain ⟨g,_,hgu,hgw⟩ := (hcycle p).2
  have hinc : inc (u j) (w p) := by
    have hg := g.property
    rw [hgu,hgw,incidencePred_succ] at hg
    exact hg
  apply hs e he f hf
  apply Or.inl
  refine ⟨?_,?_,?_⟩
  · simpa only [heu,hfu] using hlt
  · simpa only [hew,hfw] using hwp
  · simpa only [heu,hfw] using hinc

end ChvatalErdos.OrderedIncidence

#print axioms ChvatalErdos.OrderedIncidence.independent_incidence_forest
