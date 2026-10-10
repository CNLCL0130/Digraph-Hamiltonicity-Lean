import ChvatalErdos.PathBridges

set_option autoImplicit false

namespace ChvatalErdos

/-- A simple directed cycle represented by cutting it at one closing arc. -/
structure DCycle {V : Type} (D : Digraph V) where
  path : DPath D
  closing : D.arc path.last path.first

namespace DCycle
variable {V : Type} [DecidableEq V] {D : Digraph V}

theorem length_ge_two (C : DCycle D) : 2 ≤ C.path.vertices.length := by
  obtain ⟨v,l,hl⟩ := List.exists_cons_of_ne_nil C.path.nonempty
  cases l with
  | nil =>
    have hh := C.closing
    have he : D.arc v v := by simpa [DPath.first,DPath.last,hl] using hh
    exact (D.loopless v he).elim
  | cons w l => simp [hl]

theorem cyclic_arc (C : DCycle D) (i : Fin C.path.vertices.length) :
    D.arc (C.path.vertices.get i) (C.path.vertices.get (cyclicSucc i)) := by
  have hn := C.length_ge_two
  by_cases hi : i.val+1 < C.path.vertices.length
  · have hs : (cyclicSucc i).val = i.val+1 := Nat.mod_eq_of_lt hi
    have he := List.isChain_iff_getElem.mp C.path.chain i.val hi
    simpa only [List.get_eq_getElem,hs] using he
  · have hi' : i.val = C.path.vertices.length-1 := by have := i.isLt; omega
    have hs : (cyclicSucc i).val = 0 := by
      change (i.val+1) % C.path.vertices.length = 0
      have he : i.val+1 = C.path.vertices.length := by have := i.isLt; omega
      rw [he,Nat.mod_self]
    have he := C.closing
    simpa only [List.get_eq_getElem,hi',hs,DPath.first,DPath.last,
      List.getLast_eq_getElem,List.getElem_zero_eq_head] using he

end DCycle

/-- A spanning simple directed cycle gives the exact Hamiltonian definition
used by the quantitative and asymptotic targets. -/
theorem hamiltonian_of_spanning_cycle {n : Nat} {D : Digraph (Fin n)} (C : DCycle D)
    (hspan : ∀ v, v ∈ C.path.support) : Hamiltonian D := by
  have hlen : C.path.vertices.length = n := by
    have hcard := List.toFinset_card_of_nodup C.path.nodup
    have hs : C.path.support = Finset.univ := Finset.eq_univ_iff_forall.mpr hspan
    change C.path.support.card = C.path.vertices.length at hcard
    rw [hs,Finset.card_univ,Fintype.card_fin] at hcard
    exact hcard.symm
  let e : Fin n → Fin C.path.vertices.length := Fin.cast hlen.symm
  have he : Function.Bijective e := (Fin.castOrderIso hlen.symm).bijective
  let order : Fin n → Fin n := fun i => C.path.vertices.get (e i)
  refine ⟨by have := C.length_ge_two; omega,order,?_,?_,?_⟩
  · intro i j hij
    exact he.1 (List.nodup_iff_injective_get.mp C.path.nodup hij)
  · intro v
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((C.path.mem_support v).1 (hspan v))
    obtain ⟨j,hj⟩ := he.2 i
    exact ⟨j,by simpa only [order,hj] using hi⟩
  · intro i
    have hs : e (cyclicSucc i) = cyclicSucc (e i) := by
      apply Fin.ext
      simp only [e,Fin.coe_cast,cyclicSucc,hlen]
    simpa only [order,hs] using C.cyclic_arc (e i)

end ChvatalErdos

#print axioms ChvatalErdos.hamiltonian_of_spanning_cycle
