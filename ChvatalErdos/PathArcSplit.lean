import ChvatalErdos.DirectedPaths

set_option autoImplicit false

namespace ChvatalErdos
namespace DPath
variable {V : Type} [DecidableEq V] {D : Digraph V}

theorem no_arc_iff (P : DPath D) (u v : V) :
    ¬ P.HasArc u v ↔ P.vertices.IsChain (fun x y => ¬(x = u ∧ y = v)) := by
  constructor
  · intro h
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y l r heq hxy
    obtain ⟨rfl,rfl⟩ := hxy
    exact h ⟨l,r,heq⟩
  · intro h ⟨l,r,heq⟩
    exact List.isChain_iff_forall_rel_of_append_cons_cons.mp h heq ⟨rfl,rfl⟩

theorem arc_join_iff (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) (u v : V) :
    (P.join Q hd he).HasArc u v ↔
      P.HasArc u v ∨ Q.HasArc u v ∨ (u = P.last ∧ v = Q.first) := by
  classical
  constructor
  · intro h
    by_contra hn
    have hP : ¬P.HasArc u v := fun hP => hn (Or.inl hP)
    have hQ : ¬Q.HasArc u v := fun hQ => hn (Or.inr (Or.inl hQ))
    have hb : ¬(u = P.last ∧ v = Q.first) := fun hb => hn (Or.inr (Or.inr hb))
    apply (no_arc_iff (P.join Q hd he) u v).mpr ?_ h
    apply ((P.no_arc_iff u v).mp hP).append ((Q.no_arc_iff u v).mp hQ)
    intro x hx y hy ⟨hxu,hyv⟩
    have hx' : x = P.last := by simpa [last,List.getLast?_eq_getLast P.nonempty] using hx.symm
    have hy' : y = Q.first := by simpa [first,List.head?_eq_head Q.nonempty] using hy.symm
    exact hb ⟨hxu.symm.trans hx',hyv.symm.trans hy'⟩
  · rintro (h | h | ⟨rfl,rfl⟩)
    · exact P.arc_join_left Q hd he u v h
    · exact P.arc_join_right Q hd he u v h
    · refine ⟨P.vertices.dropLast,Q.vertices.tail,?_⟩
      change P.vertices ++ Q.vertices = _
      have hp := List.dropLast_append_getLast P.nonempty
      have hq := List.cons_head_tail Q.nonempty
      change P.vertices.dropLast ++ [P.last] = P.vertices at hp
      change Q.first :: Q.vertices.tail = Q.vertices at hq
      calc
        P.vertices ++ Q.vertices =
            (P.vertices.dropLast ++ [P.last]) ++ (Q.first :: Q.vertices.tail) := by
              rw [hp,hq]
        _ = _ := by simp [List.append_assoc]

/-- Split a simple path at a specified arc; both pieces are nonempty. -/
theorem split_at_arc (P : DPath D) (u v : V) (h : P.HasArc u v) :
    ∃ A B : DPath D, P.vertices = A.vertices ++ B.vertices ∧
      Disjoint A.support B.support ∧ A.first = P.first ∧ B.last = P.last ∧
      A.last = u ∧ B.first = v := by
  obtain ⟨l,r,heq⟩ := h
  have heq' : P.vertices = (l ++ [u]) ++ (v :: r) := by simpa [List.append_assoc] using heq
  have hn := List.nodup_append.mp (heq' ▸ P.nodup)
  have hc := List.isChain_append.mp (heq' ▸ P.chain)
  let A : DPath D := ⟨l ++ [u],by simp,hn.1,hc.1⟩
  let B : DPath D := ⟨v :: r,by simp,hn.2.1,hc.2.1⟩
  refine ⟨A,B,heq',?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact hn.2.2 w ((A.mem_support w).1 hw) w ((B.mem_support w).1 hw') rfl
  · simp only [first,A]
    cases l <;> simp_all
  · simp [last,B,heq]
  · simp [last,A]
  · rfl

end DPath
end ChvatalErdos

#print axioms ChvatalErdos.DPath.arc_join_iff
#print axioms ChvatalErdos.DPath.split_at_arc


