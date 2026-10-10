import ChvatalErdos.PathExpansion

set_option autoImplicit false

namespace ChvatalErdos
namespace DPath
variable {V : Type} [DecidableEq V] {D : Digraph V}

def bridge (P Q R : DPath D) (hPQ : Disjoint P.support Q.support)
    (hPR : Disjoint P.support R.support) (hQR : Disjoint Q.support R.support)
    (ePQ : D.arc P.last Q.first) (eQR : D.arc Q.last R.first) : DPath D :=
  (P.join Q hPQ ePQ).join R (by
    rw [support_join]
    exact Finset.disjoint_union_left.mpr ⟨hPR,hQR⟩)
    (by simpa only [last_join] using eQR)

theorem support_bridge (P Q R : DPath D) (hPQ : Disjoint P.support Q.support)
    (hPR : Disjoint P.support R.support) (hQR : Disjoint Q.support R.support)
    (ePQ : D.arc P.last Q.first) (eQR : D.arc Q.last R.first) :
    (P.bridge Q R hPQ hPR hQR ePQ eQR).support = P.support ∪ Q.support ∪ R.support := by
  simp only [bridge,support_join]

theorem vertices_bridge (P Q R : DPath D) (hPQ : Disjoint P.support Q.support)
    (hPR : Disjoint P.support R.support) (hQR : Disjoint Q.support R.support)
    (ePQ : D.arc P.last Q.first) (eQR : D.arc Q.last R.first) :
    (P.bridge Q R hPQ hPR hQR ePQ eQR).vertices = P.vertices ++ Q.vertices ++ R.vertices := rfl

theorem first_bridge (P Q R : DPath D) (hPQ : Disjoint P.support Q.support)
    (hPR : Disjoint P.support R.support) (hQR : Disjoint Q.support R.support)
    (ePQ : D.arc P.last Q.first) (eQR : D.arc Q.last R.first) :
    (P.bridge Q R hPQ hPR hQR ePQ eQR).first = P.first := by
  simp only [bridge,first_join]

theorem last_bridge (P Q R : DPath D) (hPQ : Disjoint P.support Q.support)
    (hPR : Disjoint P.support R.support) (hQR : Disjoint Q.support R.support)
    (ePQ : D.arc P.last Q.first) (eQR : D.arc Q.last R.first) :
    (P.bridge Q R hPQ hPR hQR ePQ eQR).last = R.last := by
  simp only [bridge,last_join]

theorem arcs_bridge (P Q R : DPath D) (hPQ : Disjoint P.support Q.support)
    (hPR : Disjoint P.support R.support) (hQR : Disjoint Q.support R.support)
    (ePQ : D.arc P.last Q.first) (eQR : D.arc Q.last R.first) (u v : V)
    (h : P.HasArc u v ∨ Q.HasArc u v ∨ R.HasArc u v) :
    (P.bridge Q R hPQ hPR hQR ePQ eQR).HasArc u v := by
  rcases h with h | h | h
  · exact (P.join Q hPQ ePQ).arc_join_left R _ _ u v (P.arc_join_left Q hPQ ePQ u v h)
  · exact (P.join Q hPQ ePQ).arc_join_left R _ _ u v (P.arc_join_right Q hPQ ePQ u v h)
  · exact (P.join Q hPQ ePQ).arc_join_right R _ _ u v h

end DPath

/-- Merge two equal-sized families using a disjoint family of connectors.
Every old arc survives and each new endpoint is an old endpoint. -/
theorem merge_path_families {V : Type} [DecidableEq V] {D : Digraph V} {r : Nat}
    (A B Q : Fin r → DPath D) (target : Equiv.Perm (Fin r))
    (hA : ∀ i j, i ≠ j → Disjoint (A i).support (A j).support)
    (hB : ∀ i j, i ≠ j → Disjoint (B i).support (B j).support)
    (hQ : ∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support)
    (hAB : ∀ i j, Disjoint (A i).support (B j).support)
    (hAQ : ∀ i j, Disjoint (A i).support (Q j).support)
    (hBQ : ∀ i j, Disjoint (B i).support (Q j).support)
    (eAQ : ∀ i, D.arc (A i).last (Q i).first)
    (eQB : ∀ i, D.arc (Q i).last (B (target i)).first) :
    ∃ P : Fin r → DPath D,
      (∀ i, (P i).vertices = (A i).vertices ++ (Q i).vertices ++ (B (target i)).vertices ∧
        (P i).first = (A i).first ∧ (P i).last = (B (target i)).last) ∧
      (∀ i j, i ≠ j → Disjoint (P i).support (P j).support) ∧
      ∀ u v, (∃ i, (A i).HasArc u v ∨ (B i).HasArc u v) → ∃ i, (P i).HasArc u v := by
  let P := fun i => (A i).bridge (Q i) (B (target i))
    (hAQ i i) (hAB i (target i)) (hBQ (target i) i).symm (eAQ i) (eQB i)
  refine ⟨P,?_,?_,?_⟩
  · intro i
    exact ⟨rfl,DPath.first_bridge _ _ _ _ _ _ _ _,DPath.last_bridge _ _ _ _ _ _ _ _⟩
  · intro i j hij
    have htij : target i ≠ target j := fun h => hij (target.injective h)
    simp only [P,DPath.support_bridge,Finset.disjoint_union_left,Finset.disjoint_union_right]
    simp only [hA i j hij,hAQ i j,hAB i (target j),(hAQ j i).symm,
      hQ i j hij,(hBQ (target j) i).symm,(hAB j (target i)).symm,
      hBQ (target i) j,hB (target i) (target j) htij,and_self]
  · intro u v huv
    obtain ⟨i,hi | hi⟩ := huv
    · exact ⟨i,DPath.arcs_bridge _ _ _ _ _ _ _ _ u v (Or.inl hi)⟩
    · refine ⟨target.symm i,DPath.arcs_bridge _ _ _ _ _ _ _ _ u v (Or.inr (Or.inr ?_))⟩
      simpa only [target.apply_symm_apply] using hi

end ChvatalErdos

#print axioms ChvatalErdos.merge_path_families

