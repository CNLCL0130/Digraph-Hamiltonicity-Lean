import ChvatalErdos.LevelChordCycle
import ChvatalErdos.CutMass

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.RootedParent
variable {n k : Nat} {D : Digraph (Fin n)} {U : Finset (Fin n)} (T : RootedParent D U)

theorem mass_level_bound (hk : 3 ≤ k) (hno : ∀ Q : UCycle D (2*k), False)
    (i : Nat) (hi : 0 < i) (hik : i < k) :
    edgeMass D (T.level i) ≤ 4*((k : ℝ)-1)*(T.level i).card := by
  apply mass_of_no_bipartite_chorded D (T.level i) hk
  intro C hCS colour hC
  have hCU : C.cycle.support ⊆ U := hCS.trans (T.level_subset i)
  have hlevel : ∀ v ∈ C.cycle.support, T.depth v = i := by
    intro v hv
    exact ((T.mem_level i v).mp (hCS hv)).2
  obtain ⟨Q⟩ := T.cycle_from_level_chord C (by omega) colour hC false i hi hik hCU
    (fun v hv => (hlevel v hv).ge) (fun v hv _ => hlevel v hv)
  exact hno Q

theorem mass_between_bound (hk : 3 ≤ k) (hno : ∀ Q : UCycle D (2*k), False)
    (i : Nat) (hi : 0 < i) (hik : i < k) :
    crossMass D (T.level i) (T.level (i+1)) ≤ ((k : ℝ)-1)*((T.level i).card+(T.level (i+1)).card) := by
  let colour := fun v => decide (T.depth v = i)
  let G := bipartiteCut D colour
  let W := T.level i ∪ T.level (i+1)
  have hW : ∀ v ∈ W, v ∈ U ∧ i ≤ T.depth v := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hh := (T.mem_level i v).mp hv
      exact ⟨hh.1,hh.2.ge⟩
    · have hh := (T.mem_level (i+1) v).mp hv
      exact ⟨hh.1,by omega⟩
  have hnoc : ∀ C : ChordedCycle G k, ¬C.cycle.support ⊆ W := by
    intro C hCS
    have hC : C.forgetCut.IsBipartite colour := ⟨fun j => (C.cycle.edge j).1.2,C.chord_edge.1.2⟩
    obtain ⟨Q⟩ := T.cycle_from_level_chord C.forgetCut (by omega) colour hC true i hi hik
      (fun v hv => (hW v (hCS hv)).1) (fun v hv => (hW v (hCS hv)).2)
      (fun v _ hv => by simpa only [colour,decide_eq_true_eq] using hv)
    exact hno Q
  have hmass := bipartite_mass_of_no_chorded G W hk colour (fun _ _ he => he.1.2) hnoc
  have hd := T.level_disjoint i (i+1) (by omega)
  have hA : ∀ v ∈ T.level i, colour v = true := by intro v hv; simp only [colour,((T.mem_level i v).mp hv).2,decide_true]
  have hB : ∀ v ∈ T.level (i+1), colour v = false := by intro v hv; simp [colour,((T.mem_level (i+1) v).mp hv).2]
  have heq := cut_union_mass D (T.level i) (T.level (i+1)) hd colour hA hB
  change edgeMass (bipartiteCut D colour) (T.level i ∪ T.level (i+1)) ≤ _ at hmass
  rw [heq] at hmass
  have hcard : (W.card : ℝ) = (T.level i).card+(T.level (i+1)).card := by
    dsimp [W]
    rw [Finset.card_union_of_disjoint hd,Nat.cast_add]
  rw [hcard] at hmass
  linarith

end ChvatalErdos.RootedParent

#print axioms ChvatalErdos.RootedParent.mass_level_bound
#print axioms ChvatalErdos.RootedParent.mass_between_bound
