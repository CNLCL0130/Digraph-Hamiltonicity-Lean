import ChvatalErdos.LayerMerge

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

theorem halfUp_iterate_le (p k : Nat) : halfUp^[k] p ≤ p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hh : halfUp (halfUp^[k] p) ≤ halfUp^[k] p := by unfold halfUp; omega
    exact hh.trans ih

variable {V : Type} [DecidableEq V] {D : Digraph V} {p a l : Nat}

/-- Iterate actual linkage-and-halving rounds. The set U records the entire
resource paths used so far, so all unused paths remain available for insertion. -/
theorem iterate_layers (F₀ : Fin p → DPath D) (sizes : Fin l → Nat)
    (J : ∀ j, Digraph (Fin (sizes j))) (R : (Σ j : Fin l, Fin (sizes j)) → DPath D)
    (hp : p ≤ a) (hJ : ∀ j, KStrong (J j) a)
    (hF₀ : ∀ i j, i ≠ j → Disjoint (F₀ i).support (F₀ j).support)
    (hR : ∀ u v, u ≠ v → Disjoint (R u).support (R v).support)
    (hF₀R : ∀ i w, Disjoint (F₀ i).support (R w).support)
    (he : ∀ j u v, (J j).arc u v → D.arc (R ⟨j,u⟩).last (R ⟨j,v⟩).first)
    (hout : ∀ j i, a ≤ (Finset.univ.filter (fun w => D.arc (F₀ i).last (R ⟨j,w⟩).first)).card)
    (hinn : ∀ j i, a ≤ (Finset.univ.filter (fun w => D.arc (R ⟨j,w⟩).last (F₀ i).first)).card)
    (k : Nat) (hk : k ≤ l) :
    ∃ F : Fin (halfUp^[k] p) → DPath D, ∃ U : Finset (Σ j : Fin l, Fin (sizes j)),
      (∀ i j, i ≠ j → Disjoint (F i).support (F j).support) ∧
      (∀ w ∈ U, w.1.val < k) ∧
      (∀ z, (∃ i, z ∈ (F i).support) ↔ (∃ i, z ∈ (F₀ i).support) ∨ ∃ w ∈ U, z ∈ (R w).support) ∧
      (∀ u v, (∃ i, (F₀ i).HasArc u v) → ∃ i, (F i).HasArc u v) ∧
      (∀ i, ∃ j, (F i).first = (F₀ j).first) ∧ (∀ i, ∃ j, (F i).last = (F₀ j).last) := by
  induction k with
  | zero =>
    refine ⟨F₀,∅,hF₀,?_,?_,?_,?_,?_⟩
    · simp
    · intro z; simp
    · intro u v huv; exact huv
    · intro i; exact ⟨i,rfl⟩
    · intro i; exact ⟨i,rfl⟩
  | succ k ih =>
    obtain ⟨F,U,hF,hUsed,hcov,harcs,hfirst,hlast⟩ := ih (by omega)
    let j : Fin l := ⟨k,by omega⟩
    have hFU : ∀ i w, Disjoint (F i).support (R ⟨j,w⟩).support := by
      intro i w
      apply Finset.disjoint_left.mpr
      intro z hz hzR
      rcases (hcov z).1 ⟨i,hz⟩ with ⟨i₀,hz₀⟩ | ⟨v,hv,hzv⟩
      · exact Finset.disjoint_left.mp (hF₀R i₀ ⟨j,w⟩) hz₀ hzR
      · have hvne : v ≠ ⟨j,w⟩ := by
          intro heq
          have hh := hUsed v hv
          rw [heq] at hh
          change k < k at hh
          omega
        exact Finset.disjoint_left.mp (hR v ⟨j,w⟩ hvne) hzv hzR
    have hRj : ∀ u v, u ≠ v → Disjoint (R ⟨j,u⟩).support (R ⟨j,v⟩).support := by
      intro u v huv
      apply hR
      intro heq
      exact huv (by simpa using heq)
    have houtF : ∀ i, a ≤ (Finset.univ.filter (fun w => D.arc (F i).last (R ⟨j,w⟩).first)).card := by
      intro i
      obtain ⟨i₀,hi₀⟩ := hlast i
      rw [hi₀]
      exact hout j i₀
    have hinnF : ∀ i, a ≤ (Finset.univ.filter (fun w => D.arc (R ⟨j,w⟩).last (F i).first)).card := by
      intro i
      obtain ⟨i₀,hi₀⟩ := hfirst i
      rw [hi₀]
      exact hinn j i₀
    obtain ⟨P,Q,hPP,hQQ,hcoverP,harcsP,hfirstP,hlastP⟩ := halving_with_layer F (J j) (hJ j)
      ((Nat.div_le_self _ _).trans ((halfUp_iterate_le p k).trans hp)) (fun w => R ⟨j,w⟩)
      hF hRj hFU (he j) houtF hinnF
    let added : Finset (Σ j : Fin l, Fin (sizes j)) :=
      Finset.univ.biUnion (fun i => (Q i).support.image (fun w => ⟨j,w⟩))
    have hadd : ∀ v, v ∈ added ↔ ∃ i w, w ∈ (Q i).support ∧ Sigma.mk j w = v := by
      intro v
      simp [added]
    rw [Function.iterate_succ_apply']
    refine ⟨P,U ∪ added,hPP,?_,?_,?_,?_,?_⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Nat.lt.step (hUsed v hv)
      · obtain ⟨i,w,_,rfl⟩ := (hadd v).1 hv
        change k < k+1
        omega
    · intro z
      rw [hcoverP,hcov]
      constructor
      · rintro ((hz₀ | ⟨v,hv,hzv⟩) | ⟨i,w,hw,hzw⟩)
        · exact Or.inl hz₀
        · exact Or.inr ⟨v,Finset.mem_union_left _ hv,hzv⟩
        · exact Or.inr ⟨⟨j,w⟩,Finset.mem_union_right _ ((hadd _).2 ⟨i,w,hw,rfl⟩),hzw⟩
      · rintro (hz₀ | ⟨v,hv,hzv⟩)
        · exact Or.inl (Or.inl hz₀)
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact Or.inl (Or.inr ⟨v,hv,hzv⟩)
          · obtain ⟨i,w,hw,rfl⟩ := (hadd v).1 hv
            exact Or.inr ⟨i,w,hw,hzv⟩
    · intro u v huv
      exact harcsP u v (harcs u v huv)
    · intro i
      obtain ⟨q,hq⟩ := hfirstP i
      obtain ⟨q₀,hq₀⟩ := hfirst q
      exact ⟨q₀,hq.trans hq₀⟩
    · intro i
      obtain ⟨q,hq⟩ := hlastP i
      obtain ⟨q₀,hq₀⟩ := hlast q
      exact ⟨q₀,hq.trans hq₀⟩

end ChvatalErdos

#print axioms ChvatalErdos.iterate_layers
