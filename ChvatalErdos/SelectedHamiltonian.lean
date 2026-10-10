import ChvatalErdos.SelectedLayers
import ChvatalErdos.CycleInsertionLinks
import ChvatalErdos.BidirectionalInsertion

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints
variable {n m b l a p : Nat}

theorem hamiltonian_from_selected_paths (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (x : Fin m → Choice b l) (F : Fin p → DPath D)
    (hp0 : 1 ≤ p) (hp : p ≤ a) (hl : Nat.clog 2 a+1 ≤ l)
    (hJ : ∀ j, KStrongOn (auxiliary D Q hb x) (active x j) a)
    (hQ : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hF : ∀ i k, i ≠ k → Disjoint (F i).support (F k).support)
    (hFQ : ∀ i w, Disjoint (F i).support ((Q w).selectedPath hb (x w)).support)
    (hout : ∀ j i, a ≤ ((active x j).filter (fun w => D.arc (F i).last ((Q w).selectedPath hb (x w)).first)).card)
    (hinn : ∀ j i, a ≤ ((active x j).filter (fun w => D.arc ((Q w).selectedPath hb (x w)).last (F i).first)).card)
    (hretained : ∀ w, (∃ i, (F i).HasArc ((Q w).retainedTail hb (x w)) ((Q w).retainedHead hb (x w))) ∨
      ∃ i, (F i).HasArc ((Q w).retainedHead hb (x w)) ((Q w).retainedTail hb (x w)))
    (hspan : ∀ z, (∃ i, z ∈ (F i).support) ∨ ∃ w, z ∈ ((Q w).selectedPath hb (x w)).support) :
    Hamiltonian D := by
  obtain ⟨C,U,hcov,harcs,havoid⟩ := cycle_from_selected_paths D Q hb x F hp0 hp hl hJ hQ hF hFQ hout hinn
  have hsub : ∀ i, ((Q i).selectedPath hb (x i)).support ⊆ (Q i).support := by
    intro i
    rw [← (Q i).selected_cover hb (x i)]
    exact Finset.subset_union_left
  apply hamiltonian_by_bidirectional_insertions C U
    (fun w => (Q w).selectedPath hb (x w))
    (fun w => (Q w).insertForward hb (x w))
    (fun w => (Q w).insertBackward hb (x w))
    (fun w => (Q w).retainedTail hb (x w))
    (fun w => (Q w).retainedHead hb (x w))
  · exact fun w => ((Q w).insertion_support hb (x w)).1
  · exact fun w => ((Q w).insertion_support hb (x w)).2
  · intro w hw z hz
    exact (hcov z).2 (Or.inr ⟨w,hw,hz⟩)
  · exact havoid
  · intro i k hik
    exact Finset.disjoint_left.mpr (fun z hzi hzk => Finset.disjoint_left.mp (hQ i k hik) (hsub i hzi) (hsub k hzk))
  · intro w _
    exact (hretained w).elim (fun h => Or.inl (harcs _ _ h)) (fun h => Or.inr (harcs _ _ h))
  · intro i k hsame
    by_contra hik
    have hd := Finset.disjoint_left.mp (hQ i k hik)
    have hi := (Q i).retained_end_mem hb (x i)
    have hk := (Q k).retained_end_mem hb (x k)
    rcases hsame with h | h | h | h
    · exact hd hi.1 (h ▸ hk.1)
    · exact hd hi.1 (h ▸ hk.2)
    · exact hd hi.2 (h ▸ hk.1)
    · exact hd hi.2 (h ▸ hk.2)
  · exact fun w => ((Q w).insertion_links hb (x w)).1
  · exact fun w => ((Q w).insertion_links hb (x w)).2.1
  · exact fun w => ((Q w).insertion_links hb (x w)).2.2.1
  · exact fun w => ((Q w).insertion_links hb (x w)).2.2.2
  · intro z
    exact (hspan z).elim (fun hz => Or.inl ((hcov z).2 (Or.inl hz))) Or.inr

end ChvatalErdos

#print axioms ChvatalErdos.hamiltonian_from_selected_paths
