import ChvatalErdos.CycleInsertion

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {V : Type} [DecidableEq V] {D : Digraph V} {n a : Nat}

/-- Close the final path through a fresh auxiliary layer, preserving all of
its old arcs and traversing each selected represented path in full. -/
theorem close_with_layer (P : DPath D) (J : Digraph (Fin n)) (hJ : KStrong J a) (ha : 1 ≤ a)
    (repr : Fin n → DPath D)
    (hR : ∀ i j, i ≠ j → Disjoint (repr i).support (repr j).support)
    (hPR : ∀ i, Disjoint P.support (repr i).support)
    (he : ∀ i j, J.arc i j → D.arc (repr i).last (repr j).first)
    (hout : a ≤ (Finset.univ.filter (fun w => D.arc P.last (repr w).first)).card)
    (hinn : a ≤ (Finset.univ.filter (fun w => D.arc (repr w).last P.first)).card) :
    ∃ C : DCycle D, ∃ Q : DPath J,
      (∀ z, z ∈ C.path.support ↔ z ∈ P.support ∨ ∃ w ∈ Q.support, z ∈ (repr w).support) ∧
      (∀ u v, P.HasArc u v → C.HasArc u v) ∧
      ∀ w ∈ Q.support, (repr w).vertices.IsInfix C.path.vertices := by
  let out := fun _ : Fin 1 => Finset.univ.filter (fun w => D.arc P.last (repr w).first)
  let inn := fun _ : Fin 1 => Finset.univ.filter (fun w => D.arc (repr w).last P.first)
  obtain ⟨Q,target,hends,hdis⟩ := strong_set_linkage J hJ ha out inn (fun _ => hout) (fun _ => hinn)
  let R := (Q 0).expand repr hR he
  have hd : Disjoint P.support R.support := by
    apply Finset.disjoint_left.mpr
    intro z hz hzR
    obtain ⟨w,_,hzw⟩ := (Q 0).mem_expand repr hR he z |>.1 hzR
    exact Finset.disjoint_left.mp (hPR w) hz hzw
  have hstart : D.arc P.last R.first := by
    change D.arc P.last ((Q 0).expand repr hR he).first
    rw [DPath.first_expand]
    exact (Finset.mem_filter.mp (hends 0).1).2
  have hfinish : D.arc R.last P.first := by
    change D.arc ((Q 0).expand repr hR he).last P.first
    rw [DPath.last_expand]
    exact (Finset.mem_filter.mp (hends 0).2).2
  let C := DCycle.close_paths P R hd hstart hfinish
  refine ⟨C,Q 0,?_,?_,?_⟩
  · intro z
    change z ∈ (P.join R hd hstart).support ↔ _
    rw [DPath.support_join,Finset.mem_union]
    exact or_congr Iff.rfl ((Q 0).mem_expand repr hR he z)
  · intro u v huv
    exact (DCycle.close_paths_arcs P R hd hstart hfinish u v).2 (Or.inl huv)
  · intro w hw
    have hi := (Q 0).whole_path_expand repr hR he w hw
    change (repr w).vertices.IsInfix (P.vertices ++ R.vertices)
    exact hi.trans (List.IsSuffix.isInfix (List.suffix_append _ _))

end ChvatalErdos

#print axioms ChvatalErdos.close_with_layer
