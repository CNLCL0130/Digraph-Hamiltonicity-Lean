import ChvatalErdos.InitialForest
import ChvatalErdos.SelectedHamiltonian

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints
variable {n m b l a : Nat}

theorem hamiltonian_from_forest_selection (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hm : 0 < m) (x : Fin m → Choice b l) (H : Finset (UPath D))
    (hα : AlphaTwoLE D a) (hH : Forest.Valid H)
    (hQ : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hHQ : ∀ P ∈ H, ∀ i, Disjoint P.support (Q i).support)
    (hcover : ∀ z, Forest.Covers H z ∨ ∃ w, z ∈ (Q w).support)
    (hl : Nat.clog 2 a+1 ≤ l)
    (hJ : ∀ j, KStrongOn (auxiliary D Q hb x) (active x j) a)
    (hout : ∀ j z, (Forest.IsEnd H z ∨ ∃ w, z ∈ (Q w).support) →
      a ≤ ((active x j).filter (fun w => D.arc z ((Q w).selectedPath hb (x w)).first)).card)
    (hinn : ∀ j z, (Forest.IsEnd H z ∨ ∃ w, z ∈ (Q w).support) →
      a ≤ ((active x j).filter (fun w => D.arc ((Q w).selectedPath hb (x w)).last z)).card) :
    Hamiltonian D := by
  obtain ⟨p,F,hp0,hp,hF,hFQ,hFcov,hretained,hfirst,hlast⟩ := initial_forest D Q hb hm x H hα hH hQ hHQ
  apply hamiltonian_from_selected_paths D Q hb x F hp0 hp hl hJ hQ hF hFQ
    (fun j i => hout j _ (hlast i)) (fun j i => hinn j _ (hfirst i)) hretained
  intro z
  rcases hcover z with hzH | ⟨w,hzw⟩
  · exact Or.inl ((hFcov z).2 (Or.inl hzH))
  · rw [← (Q w).selected_cover hb (x w)] at hzw
    rcases Finset.mem_union.mp hzw with hzP | hzS
    · exact Or.inr ⟨w,hzP⟩
    · exact Or.inl ((hFcov z).2 (Or.inr ⟨w,hzS⟩))

end ChvatalErdos

#print axioms ChvatalErdos.hamiltonian_from_forest_selection
