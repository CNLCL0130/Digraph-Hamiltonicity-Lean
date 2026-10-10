import ChvatalErdos.CycleSegments

set_option autoImplicit false

namespace ChvatalErdos.UCycle
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

theorem segment_disjoint_ordered (Q : UCycle D b) (i j : Fin b) (L M : Nat)
    (hL : L < b) (hM : M < b) (hij : i.val+L < j.val) (hjM : j.val+M < b) :
    Disjoint (Q.segment i L hL).support (Q.segment j M hM).support := by
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨s,hs,hsz⟩ := (Q.mem_segment i L hL z).1 hzA
  obtain ⟨t,ht,htz⟩ := (Q.mem_segment j M hM z).1 hzB
  have he := congrArg Fin.val (Q.injective (hsz.trans htz.symm))
  have hsa : i.val+s < b := by omega
  have htb : j.val+t < b := by omega
  simp only [index,Nat.mod_eq_of_lt hsa,Nat.mod_eq_of_lt htb] at he
  omega

theorem wrap_segment_last (Q : UCycle D b) (s : Nat) (hs : s < b) :
    (Q.segment (index (by omega : 0 < b) (b-s)) s hs).last = Q.vertex ⟨0,by omega⟩ := by
  rw [Q.segment_last]
  congr 1
  apply Fin.ext
  change ((b-s)%b+s)%b = 0
  rw [Nat.mod_add_mod]
  have he : b-s+s = b := by omega
  rw [he,Nat.mod_self]

theorem wrap_segment_disjoint (Q : UCycle D b) (s : Nat) (hs : s < b)
    (j : Fin b) (M : Nat) (hM : M < b) (hj : 0 < j.val) (hjM : j.val+M < b-s) :
    Disjoint (Q.segment (index (by omega : 0 < b) (b-s)) s hs).support (Q.segment j M hM).support := by
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨u,hu,huz⟩ := (Q.mem_segment _ s hs z).1 hzA
  obtain ⟨v,hv,hvz⟩ := (Q.mem_segment j M hM z).1 hzB
  have he := congrArg Fin.val (Q.injective (huz.trans hvz.symm))
  have hvb : j.val+v < b := by omega
  change (((b-s)%b+u)%b) = (j.val+v)%b at he
  rw [Nat.mod_add_mod,Nat.mod_eq_of_lt hvb] at he
  by_cases hus : u = s
  · have hzero : b-s+u = b := by omega
    rw [hzero,Nat.mod_self] at he
    omega
  · have huL : b-s+u < b := by omega
    rw [Nat.mod_eq_of_lt huL] at he
    omega

end ChvatalErdos.UCycle

#print axioms ChvatalErdos.UCycle.wrap_segment_disjoint
