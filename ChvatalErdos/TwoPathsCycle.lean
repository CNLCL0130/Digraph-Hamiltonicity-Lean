import ChvatalErdos.PathInterval

set_option autoImplicit false

namespace ChvatalErdos.UPath
variable {n : Nat} {D : Digraph (Fin n)}

theorem cycle_of_two_paths (P Q : UPath D) (m l : Nat) (hm : 0 < m) (hl : 2 ≤ l)
    (hP : P.vertices.length = m+1) (hQ : Q.vertices.length = l+1)
    (hfirst : P.first = Q.first) (hlast : P.last = Q.last)
    (hinter : ∀ z ∈ P.support, z ∈ Q.support → z = Q.first ∨ z = Q.last) :
    Nonempty (UCycle D (m+l)) := by
  let I := Q.interval 1 (l-1) (by omega) (by omega)
  have hd : Disjoint P.support I.reverse.support := by
    rw [support_reverse]
    apply Finset.disjoint_left.mpr
    intro z hzP hzI
    obtain ⟨j,hjlo,hjhi,hjz⟩ := (Q.mem_interval 1 (l-1) _ _ z).mp hzI
    have hzQ : z ∈ Q.support := hjz ▸ Q.point_mem j
    rcases hinter z hzP hzQ with hz | hz
    · have he : j = ⟨0,Q.length_pos⟩ := Q.point_injective (hjz.trans (hz.trans Q.point_first.symm))
      have h := congrArg Fin.val he
      simp only [Fin.val_mk] at h
      omega
    · have he : j = ⟨Q.vertices.length-1,by have h := Q.length_pos; omega⟩ :=
        Q.point_injective (hjz.trans (hz.trans Q.point_last.symm))
      have h := congrArg Fin.val he
      simp only [Fin.val_mk] at h
      omega
  have hIf : I.first = Q.point ⟨1,by omega⟩ := Q.interval_first _ _ _ _
  have hIl : I.last = Q.point ⟨l-1,by omega⟩ := Q.interval_last _ _ _ _
  have hQl : Q.point ⟨l,by omega⟩ = Q.last := by simpa only [hQ,Nat.add_sub_cancel] using Q.point_last
  have he : TwoCycle D P.last I.reverse.first := by
    rw [first_reverse,hIl,hlast,← hQl]
    have hh := Q.point_step (l-1) (by omega)
    have heq : l-1+1 = l := by omega
    simpa only [heq] using twoCycle_symm D hh
  let R := P.join I.reverse hd he
  have hRlen : R.vertices.length = m+l := by
    simp only [R,join,List.length_append,reverse,List.length_reverse]
    rw [hP]
    change m+1+(Q.interval 1 (l-1) _ _).vertices.length = _
    rw [Q.interval_length]
    omega
  have hRf : R.first = Q.first := by rw [first_join]; exact hfirst
  have hRl : R.last = Q.point ⟨1,by omega⟩ := by rw [last_join,last_reverse]; exact hIf
  have hclose : TwoCycle D R.first (R.point ⟨m+l-1,by omega⟩) := by
    have hpoint : R.point ⟨m+l-1,by omega⟩ = R.last := by simpa only [hRlen] using R.point_last
    rw [hpoint,hRf,hRl,← Q.point_first]
    exact Q.point_step 0 (by omega)
  exact ⟨R.cyclePrefix (m+l) (by omega) (by omega) hclose⟩

end ChvatalErdos.UPath

#print axioms ChvatalErdos.UPath.cycle_of_two_paths
