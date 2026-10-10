import ChvatalErdos.ExtraPathMerge
import ChvatalErdos.HalfIndices

set_option autoImplicit false

namespace ChvatalErdos
variable {V : Type} [DecidableEq V] {D : Digraph V} {p : Nat}

/-- One complete halving round, including its odd case. -/
theorem halving_merge (F : Fin p → DPath D) (Q : Fin (p/2) → DPath D)
    (target : Equiv.Perm (Fin (p/2)))
    (hF : ∀ i j, i ≠ j → Disjoint (F i).support (F j).support)
    (hQ : ∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support)
    (hFQ : ∀ i j, Disjoint (F i).support (Q j).support)
    (eFQ : ∀ i, D.arc (F (HalfIndices.left p i)).last (Q i).first)
    (eQF : ∀ i, D.arc (Q i).last (F (HalfIndices.right p (target i))).first) :
    ∃ P : Fin (halfUp p) → DPath D,
      (∀ i j, i ≠ j → Disjoint (P i).support (P j).support) ∧
      (∀ z, (∃ i, z ∈ (P i).support) ↔ (∃ i, z ∈ (F i).support) ∨ (∃ i, z ∈ (Q i).support)) ∧
      (∀ u v, (∃ i, (F i).HasArc u v) → ∃ i, (P i).HasArc u v) ∧
      (∀ i, ∃ j, (P i).first = (F j).first) ∧ (∀ i, ∃ j, (P i).last = (F j).last) := by
  let A := fun i => F (HalfIndices.left p i)
  let B := fun i => F (HalfIndices.right p i)
  let E := fun i => F (HalfIndices.extra p i)
  have hA : ∀ i j, i ≠ j → Disjoint (A i).support (A j).support := by
    intro i j hij
    exact hF _ _ (fun h => hij (HalfIndices.left_injective p h))
  have hB : ∀ i j, i ≠ j → Disjoint (B i).support (B j).support := by
    intro i j hij
    exact hF _ _ (fun h => hij (HalfIndices.right_injective p h))
  have hE : ∀ i j, i ≠ j → Disjoint (E i).support (E j).support := by
    intro i j hij
    exact hF _ _ (fun h => hij (HalfIndices.extra_injective p h))
  obtain ⟨P₀,hP,hvertices,hextra,hcover,harcs,hfirst,hlast⟩ :=
    merge_with_extra_paths A B Q E target hA hB hQ hE
      (fun i j => hF _ _ (HalfIndices.left_ne_right p i j))
      (fun i j => hFQ _ _) (fun i j => hFQ _ _)
      (fun i j => hF _ _ (HalfIndices.left_ne_extra p i j))
      (fun i j => hF _ _ (HalfIndices.right_ne_extra p i j))
      (fun i j => (hFQ _ _).symm) eFQ eQF
  let e : Fin (halfUp p) ≃ Fin (p/2+p%2) := finCongr (HalfIndices.output_size p).symm
  let P := fun i => P₀ (e i)
  refine ⟨P,fun i j hij => hP _ _ (fun h => hij (e.injective h)),?_,?_,?_,?_⟩
  · intro z
    constructor
    · rintro ⟨i,hi⟩
      rcases (hcover z).1 ⟨e i,hi⟩ with hA | hB | hQ | hE
      · obtain ⟨j,hj⟩ := hA
        exact Or.inl ⟨HalfIndices.left p j,hj⟩
      · obtain ⟨j,hj⟩ := hB
        exact Or.inl ⟨HalfIndices.right p j,hj⟩
      · exact Or.inr hQ
      · obtain ⟨j,hj⟩ := hE
        exact Or.inl ⟨HalfIndices.extra p j,hj⟩
    · intro hz
      have h₀ : ∃ i, z ∈ (P₀ i).support := by
        apply (hcover z).2
        rcases hz with ⟨i,hi⟩ | hQ
        · rcases HalfIndices.partition p i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
          · exact Or.inl ⟨j,hi⟩
          · exact Or.inr (Or.inl ⟨j,hi⟩)
          · exact Or.inr (Or.inr (Or.inr ⟨j,hi⟩))
        · exact Or.inr (Or.inr (Or.inl hQ))
      obtain ⟨i,hi⟩ := h₀
      exact ⟨e.symm i,by simpa only [P,e.apply_symm_apply] using hi⟩
  · intro u v huv
    obtain ⟨i,hi⟩ := huv
    have h₀ : ∃ i, (P₀ i).HasArc u v := by
      apply harcs u v
      rcases HalfIndices.partition p i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
      · exact Or.inl ⟨j,Or.inl hi⟩
      · exact Or.inl ⟨j,Or.inr hi⟩
      · exact Or.inr ⟨j,hi⟩
    obtain ⟨i,hi⟩ := h₀
    exact ⟨e.symm i,by simpa only [P,e.apply_symm_apply] using hi⟩
  · intro i
    rcases hfirst (e i) with ⟨j,hj⟩ | ⟨j,hj⟩
    · exact ⟨HalfIndices.left p j,hj⟩
    · exact ⟨HalfIndices.extra p j,hj⟩
  · intro i
    rcases hlast (e i) with ⟨j,hj⟩ | ⟨j,hj⟩
    · exact ⟨HalfIndices.right p j,hj⟩
    · exact ⟨HalfIndices.extra p j,hj⟩

end ChvatalErdos

#print axioms ChvatalErdos.halving_merge
