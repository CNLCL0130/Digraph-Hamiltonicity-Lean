import ChvatalErdos.PathBridges

set_option autoImplicit false

namespace ChvatalErdos
variable {V : Type} [DecidableEq V] {D : Digraph V} {r e : Nat}

/-- Merge equal halves and carry the unpaired paths along. Taking e = 0 or
e = 1 gives the even and odd rounds of the manuscript. -/
theorem merge_with_extra_paths (A B Q : Fin r → DPath D) (E : Fin e → DPath D)
    (target : Equiv.Perm (Fin r))
    (hA : ∀ i j, i ≠ j → Disjoint (A i).support (A j).support)
    (hB : ∀ i j, i ≠ j → Disjoint (B i).support (B j).support)
    (hQ : ∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support)
    (hE : ∀ i j, i ≠ j → Disjoint (E i).support (E j).support)
    (hAB : ∀ i j, Disjoint (A i).support (B j).support)
    (hAQ : ∀ i j, Disjoint (A i).support (Q j).support)
    (hBQ : ∀ i j, Disjoint (B i).support (Q j).support)
    (hAE : ∀ i j, Disjoint (A i).support (E j).support)
    (hBE : ∀ i j, Disjoint (B i).support (E j).support)
    (hQE : ∀ i j, Disjoint (Q i).support (E j).support)
    (eAQ : ∀ i, D.arc (A i).last (Q i).first)
    (eQB : ∀ i, D.arc (Q i).last (B (target i)).first) :
    ∃ P : Fin (r+e) → DPath D,
      (∀ i j, i ≠ j → Disjoint (P i).support (P j).support) ∧
      (∀ i, (P (Fin.castAdd e i)).vertices = (A i).vertices ++ (Q i).vertices ++ (B (target i)).vertices) ∧
      (∀ i, P (Fin.natAdd r i) = E i) ∧
      (∀ z, (∃ i, z ∈ (P i).support) ↔
        (∃ i, z ∈ (A i).support) ∨ (∃ i, z ∈ (B i).support) ∨
        (∃ i, z ∈ (Q i).support) ∨ (∃ i, z ∈ (E i).support)) ∧
      (∀ u v, ((∃ i, (A i).HasArc u v ∨ (B i).HasArc u v) ∨ (∃ i, (E i).HasArc u v)) →
        ∃ i, (P i).HasArc u v) ∧
      (∀ i, (∃ j, (P i).first = (A j).first) ∨ (∃ j, (P i).first = (E j).first)) ∧
      (∀ i, (∃ j, (P i).last = (B j).last) ∨ (∃ j, (P i).last = (E j).last)) := by
  obtain ⟨M,hM,hMM,hMarcs⟩ := merge_path_families A B Q target hA hB hQ hAB hAQ hBQ eAQ eQB
  have hMs : ∀ i, (M i).support = (A i).support ∪ (Q i).support ∪ (B (target i)).support := by
    intro i
    ext z
    simp [DPath.support,(hM i).1]
  have hME : ∀ i j, Disjoint (M i).support (E j).support := by
    intro i j
    rw [hMs,Finset.disjoint_union_left,Finset.disjoint_union_left]
    exact ⟨⟨hAE i j,hQE i j⟩,hBE (target i) j⟩
  let P : Fin (r+e) → DPath D := Fin.addCases M E
  have hPl : ∀ i, P (Fin.castAdd e i) = M i := by intro i; simp [P]
  have hPr : ∀ i, P (Fin.natAdd r i) = E i := by intro i; simp [P]
  refine ⟨P,?_,?_,hPr,?_,?_,?_,?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro u j
      refine Fin.addCases ?_ ?_ j
      · intro v huv
        rw [hPl,hPl]
        exact hMM u v (fun h => huv (congrArg (Fin.castAdd e) h))
      · intro v _
        rw [hPl,hPr]
        exact hME u v
    · intro u j
      refine Fin.addCases ?_ ?_ j
      · intro v _
        rw [hPr,hPl]
        exact (hME v u).symm
      · intro v huv
        rw [hPr,hPr]
        exact hE u v (fun h => huv (congrArg (Fin.natAdd r) h))
  · intro i
    rw [hPl]
    exact (hM i).1
  · intro z
    constructor
    · rintro ⟨i,hi⟩
      revert hi
      refine Fin.addCases ?_ ?_ i
      · intro j hj
        rw [hPl,hMs] at hj
        rcases Finset.mem_union.mp hj with hj | hj
        · rcases Finset.mem_union.mp hj with hj | hj
          · exact Or.inl ⟨j,hj⟩
          · exact Or.inr (Or.inr (Or.inl ⟨j,hj⟩))
        · exact Or.inr (Or.inl ⟨target j,hj⟩)
      · intro j hj
        rw [hPr] at hj
        exact Or.inr (Or.inr (Or.inr ⟨j,hj⟩))
    · rintro (⟨i,hi⟩ | ⟨i,hi⟩ | ⟨i,hi⟩ | ⟨i,hi⟩)
      · refine ⟨Fin.castAdd e i,?_⟩
        rw [hPl,hMs]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
      · refine ⟨Fin.castAdd e (target.symm i),?_⟩
        rw [hPl,hMs,target.apply_symm_apply]
        exact Finset.mem_union_right _ hi
      · refine ⟨Fin.castAdd e i,?_⟩
        rw [hPl,hMs]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
      · exact ⟨Fin.natAdd r i,by rw [hPr]; exact hi⟩
  · intro u v huv
    rcases huv with huv | ⟨i,hi⟩
    · obtain ⟨i,hi⟩ := hMarcs u v huv
      exact ⟨Fin.castAdd e i,by rw [hPl]; exact hi⟩
    · exact ⟨Fin.natAdd r i,by rw [hPr]; exact hi⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact Or.inl ⟨j,by rw [hPl]; exact (hM j).2.1⟩
    · intro j
      exact Or.inr ⟨j,by rw [hPr]⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact Or.inl ⟨target j,by rw [hPl]; exact (hM j).2.2⟩
    · intro j
      exact Or.inr ⟨j,by rw [hPr]⟩

end ChvatalErdos

#print axioms ChvatalErdos.merge_with_extra_paths
