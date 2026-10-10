import ChvatalErdos.CycleSegmentSeparation

set_option autoImplicit false

namespace ChvatalErdos.UCycle
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

theorem chord_forward_path (Q : UCycle D b) (r : Fin b) (hr : 0 < r.val)
    (he : TwoCycle D (Q.vertex ⟨0,by omega⟩) (Q.vertex r))
    (s L : Nat) (hs : s < L) (hLr : L+r.val ≤ b) :
    ∃ P : UPath D, P.support ⊆ Q.support ∧ P.vertices.length = L+1 ∧
      P.first = Q.vertex (index (by omega : 0 < b) (b-s)) ∧
      P.last = Q.vertex (index (by omega : 0 < b) (r.val+L-s-1)) := by
  let i := index (by omega : 0 < b) (b-s)
  let A := Q.segment i s (by omega)
  let B := Q.segment r (L-s-1) (by omega)
  have hd : Disjoint A.support B.support := Q.wrap_segment_disjoint s (by omega) r (L-s-1) (by omega) hr (by omega)
  have he' : TwoCycle D A.last B.first := by
    rw [Q.wrap_segment_last,Q.segment_first]
    exact he
  refine ⟨A.join B hd he',?_,?_,?_,?_⟩
  · rw [UPath.support_join]
    exact Finset.union_subset (Q.segment_support _ _ _) (Q.segment_support _ _ _)
  · simp only [UPath.join,List.length_append]
    rw [Q.segment_length,Q.segment_length]
    omega
  · rw [UPath.first_join,Q.segment_first]
  · rw [UPath.last_join,Q.segment_last]
    congr 2
    omega

theorem chord_cross_minus (Q : UCycle D b) (r : Fin b) (hr : 0 < r.val)
    (he : TwoCycle D (Q.vertex ⟨0,by omega⟩) (Q.vertex r))
    (s t : Nat) (hs : s < b-r.val) (ht : t < r.val) :
    ∃ P : UPath D, P.support ⊆ Q.support ∧ P.vertices.length = s+t+2 ∧
      P.first = Q.vertex (index (by omega : 0 < b) (b-s)) ∧
      P.last = Q.vertex (index (by omega : 0 < b) (r.val-t)) := by
  let i := index (by omega : 0 < b) (b-s)
  let j : Fin b := ⟨r.val-t,by omega⟩
  let A := Q.segment i s (by omega)
  let B := (Q.segment j t (by omega)).reverse
  have hd : Disjoint A.support B.support := by
    rw [UPath.support_reverse]
    exact Q.wrap_segment_disjoint s (by omega) j t (by omega) (by dsimp [j]; omega) (by dsimp [j]; omega)
  have he' : TwoCycle D A.last B.first := by
    rw [Q.wrap_segment_last,UPath.first_reverse,Q.segment_last]
    have hj : index (by omega : 0 < b) (j.val+t) = r := by
      apply Fin.ext
      have heq : j.val+t = r.val := by dsimp [j]; omega
      simp [index,heq,Nat.mod_eq_of_lt r.isLt]
    rw [hj]
    exact he
  refine ⟨A.join B hd he',?_,?_,?_,?_⟩
  · rw [UPath.support_join,UPath.support_reverse]
    exact Finset.union_subset (Q.segment_support _ _ _) (Q.segment_support _ _ _)
  · simp only [UPath.join,List.length_append]
    change A.vertices.length + (List.reverse (Q.segment j t _).vertices).length = s+t+2
    rw [List.length_reverse,Q.segment_length,Q.segment_length]
    omega
  · rw [UPath.first_join,Q.segment_first]
  · rw [UPath.last_join,UPath.last_reverse,Q.segment_first]
    congr 1
    apply Fin.ext
    exact (Nat.mod_eq_of_lt j.isLt).symm

theorem chord_cross_plus (Q : UCycle D b) (r : Fin b) (hr : 0 < r.val)
    (he : TwoCycle D (Q.vertex ⟨0,by omega⟩) (Q.vertex r))
    (s t : Nat) (hs : s < r.val) (ht : t < b-r.val) :
    ∃ P : UPath D, P.support ⊆ Q.support ∧ P.vertices.length = s+t+2 ∧
      P.first = Q.vertex (index (by omega : 0 < b) s) ∧
      P.last = Q.vertex (index (by omega : 0 < b) (r.val+t)) := by
  let zero : Fin b := ⟨0,by omega⟩
  let A := (Q.segment zero s (by omega)).reverse
  let B := Q.segment r t (by omega)
  have hd : Disjoint A.support B.support := by
    rw [UPath.support_reverse]
    exact Q.segment_disjoint_ordered zero r s t (by omega) (by omega) (by simpa [zero] using hs) (by omega)
  have he' : TwoCycle D A.last B.first := by
    rw [UPath.last_reverse,Q.segment_first,Q.segment_first]
    exact he
  refine ⟨A.join B hd he',?_,?_,?_,?_⟩
  · rw [UPath.support_join,UPath.support_reverse]
    exact Finset.union_subset (Q.segment_support _ _ _) (Q.segment_support _ _ _)
  · simp only [UPath.join,List.length_append]
    change (List.reverse (Q.segment zero s _).vertices).length + B.vertices.length = s+t+2
    rw [List.length_reverse,Q.segment_length,Q.segment_length]
    omega
  · rw [UPath.first_join,UPath.first_reverse,Q.segment_last]
    simp [zero]
  · rw [UPath.last_join,Q.segment_last]

end ChvatalErdos.UCycle

#print axioms ChvatalErdos.UCycle.chord_forward_path
#print axioms ChvatalErdos.UCycle.chord_cross_minus
#print axioms ChvatalErdos.UCycle.chord_cross_plus
