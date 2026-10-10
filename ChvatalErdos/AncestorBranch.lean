import ChvatalErdos.Ancestors

set_option autoImplicit false

namespace ChvatalErdos.RootedParent
variable {n : Nat} {D : Digraph (Fin n)} {U : Finset (Fin n)} (T : RootedParent D U)

theorem branch_path (a b : Fin n) (ha : a ∈ U) (hb : b ∈ U) (i q : Nat)
    (hda : T.depth a = i) (hdb : T.depth b = i) (hq : q < i)
    (hcommon : T.ancestor a q = T.ancestor b q)
    (hdifferent : T.ancestor a (q+1) ≠ T.ancestor b (q+1)) :
    ∃ P : UPath D, P.first = a ∧ P.last = b ∧ P.vertices.length = 2*(i-q)+1 ∧
      P.support ⊆ U ∧ ∀ z ∈ P.support, T.depth z < i ∨ z = a ∨ z = b := by
  let A := T.segment a ha (q+1) i (by omega) (by omega)
  let B := T.segment b hb q i (by omega) (by omega)
  have hd : Disjoint A.reverse.support B.support := by
    rw [UPath.support_reverse]
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    obtain ⟨j,hjlo,hjhi,hjz⟩ := (T.mem_segment a ha (q+1) i _ _ z).mp hzA
    obtain ⟨l,hllo,hlhi,hlz⟩ := (T.mem_segment b hb q i _ _ z).mp hzB
    have hjd := T.ancestor_depth a ha j (by omega)
    have hld := T.ancestor_depth b hb l (by omega)
    have hjl : j = l := by rw [hjz] at hjd; rw [hlz] at hld; omega
    have he : T.ancestor a j = T.ancestor b j := by rw [← hjl] at hlz; exact hjz.trans hlz.symm
    exact hdifferent (T.ancestor_prefix ha hb (q+1) j (by omega) (by omega) (by omega) he)
  have hAlast : A.reverse.last = T.ancestor a (q+1) := by
    rw [UPath.last_reverse]; exact T.segment_first a ha _ _ _ _
  have hBfirst : B.first = T.ancestor b q := T.segment_first b hb _ _ _ _
  have he : TwoCycle D A.reverse.last B.first := by
    rw [hAlast,hBfirst,← hcommon]
    exact twoCycle_symm D (T.ancestor_step a ha q (by omega))
  refine ⟨A.reverse.join B hd he,?_,?_,?_,?_,?_⟩
  · rw [UPath.first_join,UPath.first_reverse]
    change (T.segment a ha (q+1) i _ _).last = a
    rw [T.segment_last,← hda,T.ancestor_self]
  · rw [UPath.last_join]
    change (T.segment b hb q i _ _).last = b
    rw [T.segment_last,← hdb,T.ancestor_self]
  · simp only [UPath.join,UPath.reverse,List.length_append,List.length_reverse]
    change A.vertices.length+B.vertices.length = _
    dsimp [A,B]
    rw [T.segment_length,T.segment_length]
    omega
  · intro z hz
    rw [UPath.support_join,UPath.support_reverse] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨j,_,_,rfl⟩ := (T.mem_segment a ha (q+1) i _ _ z).mp hz
      exact T.ancestor_mem a ha j
    · obtain ⟨j,_,_,rfl⟩ := (T.mem_segment b hb q i _ _ z).mp hz
      exact T.ancestor_mem b hb j
  · intro z hz
    rw [UPath.support_join,UPath.support_reverse] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨j,_,hj,rfl⟩ := (T.mem_segment a ha (q+1) i _ _ z).mp hz
      by_cases hji : j < i
      · exact Or.inl (by rw [T.ancestor_depth a ha j (by omega)]; exact hji)
      · have hji : j = T.depth a := by omega
        exact Or.inr (Or.inl (by rw [hji,T.ancestor_self]))
    · obtain ⟨j,_,hj,rfl⟩ := (T.mem_segment b hb q i _ _ z).mp hz
      by_cases hji : j < i
      · exact Or.inl (by rw [T.ancestor_depth b hb j (by omega)]; exact hji)
      · have hji : j = T.depth b := by omega
        exact Or.inr (Or.inr (by rw [hji,T.ancestor_self]))

end ChvatalErdos.RootedParent

#print axioms ChvatalErdos.RootedParent.branch_path
