import ChvatalErdos.Forest
import ChvatalErdos.CycleInsertionLinks

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints
variable {n m b l a : Nat}

theorem initial_forest (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hm : 0 < m) (x : Fin m → Choice b l) (H : Finset (UPath D))
    (hα : AlphaTwoLE D a) (hH : Forest.Valid H)
    (hQ : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hHQ : ∀ P ∈ H, ∀ i, Disjoint P.support (Q i).support) :
    ∃ p, ∃ F : Fin p → DPath D,
      1 ≤ p ∧ p ≤ a ∧
      (∀ i k, i ≠ k → Disjoint (F i).support (F k).support) ∧
      (∀ i w, Disjoint (F i).support ((Q w).selectedPath hb (x w)).support) ∧
      (∀ z, (∃ i, z ∈ (F i).support) ↔ Forest.Covers H z ∨ ∃ w, z ∈ ((Q w).selectedRetained hb (x w)).support) ∧
      (∀ w, (∃ i, (F i).HasArc ((Q w).retainedTail hb (x w)) ((Q w).retainedHead hb (x w))) ∨
        ∃ i, (F i).HasArc ((Q w).retainedHead hb (x w)) ((Q w).retainedTail hb (x w))) ∧
      (∀ i, Forest.IsEnd H (F i).first ∨ ∃ w, (F i).first ∈ (Q w).support) ∧
      (∀ i, Forest.IsEnd H (F i).last ∨ ∃ w, (F i).last ∈ (Q w).support) := by
  let S := fun w => (Q w).selectedRetained hb (x w)
  let G₀ := H ∪ Finset.univ.image S
  have hSsub : ∀ i, (S i).support ⊆ (Q i).support := by
    intro i
    rw [← (Q i).selected_cover hb (x i)]
    exact Finset.subset_union_right
  have hPsub : ∀ i, ((Q i).selectedPath hb (x i)).support ⊆ (Q i).support := by
    intro i
    rw [← (Q i).selected_cover hb (x i)]
    exact Finset.subset_union_left
  have hG₀ : Forest.Valid G₀ := by
    intro P hP R hR hPR
    rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hR with hR | hR
    · exact hH P hP R hR hPR
    · obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hR
      exact Finset.disjoint_left.mpr (fun z hz hzS => Finset.disjoint_left.mp (hHQ P hP w) hz (hSsub w hzS))
    · obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hP
      exact Finset.disjoint_left.mpr (fun z hzS hz => Finset.disjoint_left.mp (hHQ R hR w) hz (hSsub w hzS))
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hR
      have hik : i ≠ k := fun h => hPR (congrArg S h)
      exact Finset.disjoint_left.mpr (fun z hzi hzk => Finset.disjoint_left.mp (hQ i k hik) (hSsub i hzi) (hSsub k hzk))
  have hG₀cov : ∀ z, Forest.Covers G₀ z ↔ Forest.Covers H z ∨ ∃ w, z ∈ (S w).support := by
    intro z
    constructor
    · rintro ⟨P,hP,hz⟩
      rcases Finset.mem_union.mp hP with hP | hP
      · exact Or.inl ⟨P,hP,hz⟩
      · obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hP
        exact Or.inr ⟨w,hz⟩
    · rintro (⟨P,hP,hz⟩ | ⟨w,hz⟩)
      · exact ⟨P,Finset.mem_union_left _ hP,hz⟩
      · exact ⟨S w,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩),hz⟩
  obtain ⟨G,hG,hExt,hGa⟩ := Forest.extension hG₀ a hα
  let e : Fin G.card ≃ G := by simpa only [Fintype.card_coe] using (Fintype.equivFin G).symm
  let F := fun i => (e i).val.orient
  have hFcov : ∀ z, (∃ i, z ∈ (F i).support) ↔ Forest.Covers G z := by
    intro z
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).val,(e i).property,hi⟩
    · rintro ⟨P,hP,hz⟩
      obtain ⟨i,hi⟩ := e.surjective ⟨P,hP⟩
      exact ⟨i,by change z ∈ (e i).val.support; rw [hi]; exact hz⟩
  have hsize : 1 ≤ G.card := by
    let w : Fin m := ⟨0,hm⟩
    have hz : Forest.Covers G₀ (S w).first := (hG₀cov _).2 (Or.inr ⟨w,(S w).first_mem⟩)
    obtain ⟨P,hP,_⟩ := (hExt.1 _).2 hz
    exact Finset.card_pos.mpr ⟨P,hP⟩
  have hEnds : ∀ z, Forest.IsEnd G z → Forest.IsEnd H z ∨ ∃ w, z ∈ (Q w).support := by
    intro z hz
    obtain ⟨P,hP,hzP⟩ := hExt.2.2 z hz
    rcases Finset.mem_union.mp hP with hP | hP
    · exact Or.inl ⟨P,hP,hzP⟩
    · obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hP
      apply Or.inr
      refine ⟨w,hSsub w ?_⟩
      rcases hzP with rfl | rfl
      · exact (S w).first_mem
      · exact (S w).last_mem
  refine ⟨G.card,F,hsize,hGa,?_,?_,?_,?_,?_,?_⟩
  · intro i k hik
    apply hG _ (e i).property _ (e k).property
    intro he
    exact hik (e.injective (Subtype.ext he))
  · intro i w
    apply Finset.disjoint_left.mpr
    intro z hz hzP
    have hzG := (hFcov z).1 ⟨i,hz⟩
    rcases (hG₀cov z).1 ((hExt.1 z).1 hzG) with ⟨P,hP,hzH⟩ | ⟨k,hzk⟩
    · exact Finset.disjoint_left.mp (hHQ P hP w) hzH (hPsub w hzP)
    · by_cases hkw : k = w
      · subst k
        exact Finset.disjoint_left.mp ((Q w).selected_disjoint hb (x w)) hzP hzk
      · exact Finset.disjoint_left.mp (hQ k w hkw) (hSsub k hzk) (hPsub w hzP)
  · intro z
    exact (hFcov z).trans ((hExt.1 z).trans (hG₀cov z))
  · intro w
    have hEdge : Forest.HasEdge G₀ ((Q w).retainedTail hb (x w)) ((Q w).retainedHead hb (x w)) :=
      ⟨S w,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩),(Q w).retained_hasEdge hb (x w)⟩
    obtain ⟨P,hP,hEdge⟩ := hExt.2.1 _ _ hEdge
    obtain ⟨i,hi⟩ := e.surjective ⟨P,hP⟩
    have hFi : F i = P.orient := by dsimp [F]; rw [hi]
    exact (P.orient_edge _ _ hEdge).elim
      (fun h => Or.inl ⟨i,by rw [hFi]; exact h⟩)
      (fun h => Or.inr ⟨i,by rw [hFi]; exact h⟩)
  · intro i
    exact hEnds _ ⟨(e i).val,(e i).property,Or.inl rfl⟩
  · intro i
    exact hEnds _ ⟨(e i).val,(e i).property,Or.inr rfl⟩

end ChvatalErdos

#print axioms ChvatalErdos.initial_forest
