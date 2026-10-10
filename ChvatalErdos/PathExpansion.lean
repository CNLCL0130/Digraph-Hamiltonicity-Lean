import ChvatalErdos.DirectedPaths
import ChvatalErdos.LinkagePaths

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
namespace DPath

variable {V W : Type} [DecidableEq V] [DecidableEq W]
    {D : Digraph V} {J : Digraph W}

/-- Replace each auxiliary vertex by its entire represented path. -/
def expand (Q : DPath J) (repr : W → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first) : DPath D where
  vertices := Q.vertices.flatMap (fun w => (repr w).vertices)
  nonempty := by
    intro hnil
    have hh := List.flatMap_eq_nil_iff.mp hnil Q.first (List.head_mem Q.nonempty)
    exact (repr Q.first).nonempty hh
  nodup := List.nodup_flatMap.mpr ⟨fun w _ => (repr w).nodup,
    Q.nodup.imp (fun {u v} huv w hwu hwv =>
      Finset.disjoint_left.mp (hd u v huv) ((repr u).mem_support w |>.2 hwu)
        ((repr v).mem_support w |>.2 hwv))⟩
  chain := by
    apply (List.isChain_flatten ?_).mpr
    · constructor
      · intro l hl
        obtain ⟨w,_,rfl⟩ := List.mem_map.mp hl
        exact (repr w).chain
      · apply (List.isChain_map _).mpr
        exact Q.chain.imp (fun u v huv x hx y hy => by
          have hx' : x = (repr u).last := by
            simpa [last,List.getLast?_eq_getLast (repr u).nonempty] using hx.symm
          have hy' : y = (repr v).first := by
            simpa [first,List.head?_eq_head (repr v).nonempty] using hy.symm
          simpa only [hx',hy'] using he u v huv)
    · intro hempty
      obtain ⟨w,_,hw⟩ := List.mem_map.mp hempty
      exact (repr w).nonempty hw

theorem mem_expand (Q : DPath J) (repr : W → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first) (x : V) :
    x ∈ (Q.expand repr hd he).support ↔ ∃ w ∈ Q.support, x ∈ (repr w).support := by
  simp only [mem_support,expand,List.mem_flatMap]

theorem first_expand (Q : DPath J) (repr : W → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first) :
    (Q.expand repr hd he).first = (repr Q.first).first := by
  obtain ⟨w,l,hw⟩ := List.exists_cons_of_ne_nil Q.nonempty
  simp [first,expand,hw,(repr w).nonempty]

theorem last_expand (Q : DPath J) (repr : W → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first) :
    (Q.expand repr hd he).last = (repr Q.last).last := by
  have hlast := List.dropLast_append_getLast Q.nonempty
  have hs : (Q.expand repr hd he).vertices.getLast? = (repr Q.last).vertices.getLast? := by
    change (Q.vertices.flatMap (fun w => (repr w).vertices)).getLast? = _
    conv_lhs => rw [← hlast]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getLast?_append]
    change (repr Q.last).vertices.getLast?.or _ = (repr Q.last).vertices.getLast?
    rw [List.getLast?_eq_getLast (repr Q.last).nonempty]
    rfl
  simpa only [List.getLast?_eq_getLast (Q.expand repr hd he).nonempty,
    List.getLast?_eq_getLast (repr Q.last).nonempty,Option.some.injEq] using hs

theorem whole_path_expand (Q : DPath J) (repr : W → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first)
    (w : W) (hw : w ∈ Q.support) :
    (repr w).vertices.IsInfix (Q.expand repr hd he).vertices := by
  apply List.infix_of_mem_flatten
  exact List.mem_map.mpr ⟨w,(Q.mem_support w).1 hw,rfl⟩

theorem disjoint_expand (Q R : DPath J) (repr : W → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first)
    (hQR : Disjoint Q.support R.support) :
    Disjoint (Q.expand repr hd he).support (R.expand repr hd he).support := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨u,hu,hxu⟩ := (Q.mem_expand repr hd he x).1 hx
  obtain ⟨v,hv,hxv⟩ := (R.mem_expand repr hd he x).1 hx'
  have huv : u ≠ v := by
    intro h
    exact Finset.disjoint_left.mp hQR hu (h ▸ hv)
  exact Finset.disjoint_left.mp (hd u v huv) hxu hxv

end DPath

/-- The internal connections required for a round of merging. Each connection
is exactly a concatenation of entire represented paths. -/

theorem represented_internal_linkage {V : Type} [DecidableEq V] {D : Digraph V}
    {n r h : Nat} (J : Digraph (Fin n)) (hJ : KStrong J h) (hr : r ≤ h)
    (repr : Fin n → DPath D)
    (hd : ∀ u v, u ≠ v → Disjoint (repr u).support (repr v).support)
    (he : ∀ u v, J.arc u v → D.arc (repr u).last (repr v).first)
    (X Y : Fin r → V)
    (hout : ∀ i, h ≤ (Finset.univ.filter (fun w => D.arc (X i) (repr w).first)).card)
    (hinn : ∀ i, h ≤ (Finset.univ.filter (fun w => D.arc (repr w).last (Y i))).card) :
    ∃ P : Fin r → DPath D, ∃ Q : Fin r → DPath J, ∃ target : Equiv.Perm (Fin r),
      (∀ i, (P i).vertices = (Q i).vertices.flatMap (fun w => (repr w).vertices) ∧
        D.arc (X i) (P i).first ∧ D.arc (P i).last (Y (target i))) ∧
      ∀ i j, i ≠ j → Disjoint (P i).support (P j).support := by
  classical
  let out : Fin r → Finset (Fin n) := fun i => Finset.univ.filter (fun w => D.arc (X i) (repr w).first)
  let inn : Fin r → Finset (Fin n) := fun i => Finset.univ.filter (fun w => D.arc (repr w).last (Y i))
  obtain ⟨Q,target,hends,hdis⟩ := strong_set_linkage J hJ hr out inn hout hinn
  refine ⟨fun i => (Q i).expand repr hd he,Q,target,?_,?_⟩
  · intro i
    refine ⟨rfl,?_,?_⟩
    · rw [DPath.first_expand]
      exact (Finset.mem_filter.mp (hends i).1).2
    · rw [DPath.last_expand]
      exact (Finset.mem_filter.mp (hends i).2).2
  · intro i j hij
    exact (Q i).disjoint_expand (Q j) repr hd he (hdis i j hij)

end ChvatalErdos

#print axioms ChvatalErdos.DPath.expand
#print axioms ChvatalErdos.DPath.whole_path_expand
#print axioms ChvatalErdos.DPath.disjoint_expand
#print axioms ChvatalErdos.represented_internal_linkage





