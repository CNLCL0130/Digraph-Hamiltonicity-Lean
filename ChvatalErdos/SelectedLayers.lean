import ChvatalErdos.ColourFibres
import ChvatalErdos.AuxiliaryGraph
import ChvatalErdos.LayerCycle

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints
variable {n m b l a p : Nat}

theorem cycle_from_selected_paths (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (x : Fin m → Choice b l) (F : Fin p → DPath D)
    (hp0 : 1 ≤ p) (hp : p ≤ a) (hl : Nat.clog 2 a+1 ≤ l)
    (hJ : ∀ j, KStrongOn (auxiliary D Q hb x) (active x j) a)
    (hQ : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hF : ∀ i k, i ≠ k → Disjoint (F i).support (F k).support)
    (hFQ : ∀ i w, Disjoint (F i).support ((Q w).selectedPath hb (x w)).support)
    (hout : ∀ j i, a ≤ ((active x j).filter (fun w => D.arc (F i).last ((Q w).selectedPath hb (x w)).first)).card)
    (hinn : ∀ j i, a ≤ ((active x j).filter (fun w => D.arc ((Q w).selectedPath hb (x w)).last (F i).first)).card) :
    ∃ C : DCycle D, ∃ U : Finset (Fin m),
      (∀ z, z ∈ C.path.support ↔ (∃ i, z ∈ (F i).support) ∨ ∃ w ∈ U, z ∈ ((Q w).selectedPath hb (x w)).support) ∧
      (∀ u v, (∃ i, (F i).HasArc u v) → C.HasArc u v) ∧
      ∀ w, w ∉ U → Disjoint C.path.support ((Q w).selectedPath hb (x w)).support := by
  let col := fun i => colour (x i)
  let sizes := ColourFibres.size col
  let idx := ColourFibres.index col
  let J := fun j => inducedDigraph (auxiliary D Q hb x) (fun w : Fin (sizes j) => idx ⟨j,w⟩)
  let R := fun w => (Q (idx w)).selectedPath hb (x (idx w))
  have hsub : ∀ i, ((Q i).selectedPath hb (x i)).support ⊆ (Q i).support := by
    intro i
    rw [← (Q i).selected_cover hb (x i)]
    exact Finset.subset_union_left
  have hR : ∀ u v, u ≠ v → Disjoint (R u).support (R v).support := by
    intro u v huv
    apply Finset.disjoint_left.mpr
    intro z hzu hzv
    exact Finset.disjoint_left.mp (hQ _ _ (fun h => huv (ColourFibres.index_injective col h)))
      (hsub _ hzu) (hsub _ hzv)
  have hJs : ∀ j, KStrong (J j) a := by
    intro j
    exact ColourFibres.induced_strong col j _ a (hJ j)
  have he : ∀ j u v, (J j).arc u v → D.arc (R ⟨j,u⟩).last (R ⟨j,v⟩).first := by
    intro j u v huv
    exact auxiliary_arc_expands D Q hb x _ _ huv
  have ho : ∀ j i, a ≤ (Finset.univ.filter (fun w => D.arc (F i).last (R ⟨j,w⟩).first)).card := by
    intro j i
    change a ≤ (Finset.univ.filter (fun w : Fin (sizes j) => D.arc (F i).last ((Q (idx ⟨j,w⟩)).selectedPath hb (x (idx ⟨j,w⟩))).first)).card
    rw [ColourFibres.filter_card col j (fun w => D.arc (F i).last ((Q w).selectedPath hb (x w)).first)]
    exact hout j i
  have hi : ∀ j i, a ≤ (Finset.univ.filter (fun w => D.arc (R ⟨j,w⟩).last (F i).first)).card := by
    intro j i
    change a ≤ (Finset.univ.filter (fun w : Fin (sizes j) => D.arc ((Q (idx ⟨j,w⟩)).selectedPath hb (x (idx ⟨j,w⟩))).last (F i).first)).card
    rw [ColourFibres.filter_card col j (fun w => D.arc ((Q w).selectedPath hb (x w)).last (F i).first)]
    exact hinn j i
  obtain ⟨C,U,hcov,harcs,havoid⟩ := cycle_from_layers F sizes J R hp0 hp hl hJs hF hR
    (fun i w => hFQ i (idx w)) he ho hi
  refine ⟨C,U.image idx,?_,harcs,?_⟩
  · intro z
    rw [hcov]
    constructor
    · rintro (hz | ⟨w,hw,hz⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨idx w,Finset.mem_image.mpr ⟨w,hw,rfl⟩,hz⟩
    · rintro (hz | ⟨w,hw,hz⟩)
      · exact Or.inl hz
      · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
        exact Or.inr ⟨v,hv,hz⟩
  · intro w hw
    obtain ⟨v,rfl⟩ := ColourFibres.index_surjective col w
    apply havoid v
    intro hv
    exact hw (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

end ChvatalErdos

#print axioms ChvatalErdos.cycle_from_selected_paths
