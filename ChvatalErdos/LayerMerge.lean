import ChvatalErdos.HalvingMerge

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {V : Type} [DecidableEq V] {D : Digraph V} {p n a : Nat}

/-- Use a fresh auxiliary layer to merge an arbitrary path family down to
half its size, rounding up. Every represented path is used in full. -/
theorem halving_with_layer (F : Fin p → DPath D) (J : Digraph (Fin n)) (hJ : KStrong J a)
    (hp : p/2 ≤ a) (repr : Fin n → DPath D)
    (hF : ∀ i j, i ≠ j → Disjoint (F i).support (F j).support)
    (hR : ∀ i j, i ≠ j → Disjoint (repr i).support (repr j).support)
    (hFR : ∀ i j, Disjoint (F i).support (repr j).support)
    (he : ∀ i j, J.arc i j → D.arc (repr i).last (repr j).first)
    (hout : ∀ i, a ≤ (Finset.univ.filter (fun w => D.arc (F i).last (repr w).first)).card)
    (hinn : ∀ i, a ≤ (Finset.univ.filter (fun w => D.arc (repr w).last (F i).first)).card) :
    ∃ P : Fin (halfUp p) → DPath D, ∃ Q : Fin (p/2) → DPath J,
      (∀ i j, i ≠ j → Disjoint (P i).support (P j).support) ∧
      (∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support) ∧
      (∀ z, (∃ i, z ∈ (P i).support) ↔ (∃ i, z ∈ (F i).support) ∨
        (∃ i w, w ∈ (Q i).support ∧ z ∈ (repr w).support)) ∧
      (∀ u v, (∃ i, (F i).HasArc u v) → ∃ i, (P i).HasArc u v) ∧
      (∀ i, ∃ j, (P i).first = (F j).first) ∧ (∀ i, ∃ j, (P i).last = (F j).last) := by
  classical
  let out := fun i : Fin (p/2) => Finset.univ.filter (fun w => D.arc (F (HalfIndices.left p i)).last (repr w).first)
  let inn := fun i : Fin (p/2) => Finset.univ.filter (fun w => D.arc (repr w).last (F (HalfIndices.right p i)).first)
  obtain ⟨Q,target,hends,hQQ⟩ := strong_set_linkage J hJ hp out inn
    (fun i => hout (HalfIndices.left p i)) (fun i => hinn (HalfIndices.right p i))
  let C := fun i => (Q i).expand repr hR he
  have hCC : ∀ i j, i ≠ j → Disjoint (C i).support (C j).support := by
    intro i j hij
    exact (Q i).disjoint_expand (Q j) repr hR he (hQQ i j hij)
  have hFC : ∀ i j, Disjoint (F i).support (C j).support := by
    intro i j
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨w,_,hzw⟩ := (Q j).mem_expand repr hR he z |>.1 hz'
    exact Finset.disjoint_left.mp (hFR i w) hz hzw
  have heFC : ∀ i, D.arc (F (HalfIndices.left p i)).last (C i).first := by
    intro i
    change D.arc _ ((Q i).expand repr hR he).first
    rw [DPath.first_expand]
    exact (Finset.mem_filter.mp (hends i).1).2
  have heCF : ∀ i, D.arc (C i).last (F (HalfIndices.right p (target i))).first := by
    intro i
    change D.arc ((Q i).expand repr hR he).last _
    rw [DPath.last_expand]
    exact (Finset.mem_filter.mp (hends i).2).2
  obtain ⟨P,hPP,hcov,harcs,hfirst,hlast⟩ := halving_merge F C target hF hCC hFC heFC heCF
  refine ⟨P,Q,hPP,hQQ,?_,harcs,hfirst,hlast⟩
  intro z
  rw [hcov]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨w,hw,hzw⟩ := (Q i).mem_expand repr hR he z |>.1 hi
    exact ⟨i,w,hw,hzw⟩
  · rintro ⟨i,w,hw,hzw⟩
    exact ⟨i,(Q i).mem_expand repr hR he z |>.2 ⟨w,hw,hzw⟩⟩

end ChvatalErdos

#print axioms ChvatalErdos.halving_with_layer
