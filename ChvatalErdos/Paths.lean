import ChvatalErdos.Core
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace ChvatalErdos

structure UPath {V : Type} (D : Digraph V) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain (TwoCycle D)

namespace UPath
variable {V : Type} [DecidableEq V] {D : Digraph V}

def first (P : UPath D) : V := P.vertices.head P.nonempty
def last (P : UPath D) : V := P.vertices.getLast P.nonempty

noncomputable def support (P : UPath D) : Finset V := by
  classical
  exact P.vertices.toFinset

theorem mem_support (P : UPath D) (v : V) : v ∈ P.support ↔ v ∈ P.vertices := by
  classical
  simp [support]

theorem first_mem (P : UPath D) : P.first ∈ P.support :=
  (P.mem_support _).2 (List.head_mem P.nonempty)

theorem last_mem (P : UPath D) : P.last ∈ P.support :=
  (P.mem_support _).2 (List.getLast_mem P.nonempty)

def reverse (P : UPath D) : UPath D where
  vertices := P.vertices.reverse
  nonempty := by simpa using P.nonempty
  nodup := by simpa using P.nodup
  chain := List.isChain_reverse.mpr (P.chain.imp (fun _ _ h => twoCycle_symm D h))

theorem support_reverse (P : UPath D) : P.reverse.support = P.support := by
  classical
  ext v
  simp [support,reverse]

theorem first_reverse (P : UPath D) : P.reverse.first = P.last := by
  simp [first,last,reverse]

theorem last_reverse (P : UPath D) : P.reverse.last = P.first := by
  simp [first,last,reverse]

def join (P Q : UPath D) (hd : Disjoint P.support Q.support) (he : TwoCycle D P.last Q.first) : UPath D where
  vertices := P.vertices ++ Q.vertices
  nonempty := by simp [P.nonempty]
  nodup := P.nodup.append Q.nodup (by
    intro v hv hv'
    exact Finset.disjoint_left.mp hd ((P.mem_support v).2 hv) ((Q.mem_support v).2 hv'))
  chain := P.chain.append Q.chain (by
    intro x hx y hy
    have hx' : x = P.last := by simpa [last,List.getLast?_eq_getLast P.nonempty] using hx.symm
    have hy' : y = Q.first := by simpa [first,List.head?_eq_head Q.nonempty] using hy.symm
    simpa [hx',hy'] using he)

theorem support_join (P Q : UPath D) (hd : Disjoint P.support Q.support) (he : TwoCycle D P.last Q.first) :
    (P.join Q hd he).support = P.support ∪ Q.support := by
  classical
  ext v
  simp [support,join]

theorem first_join (P Q : UPath D) (hd : Disjoint P.support Q.support) (he : TwoCycle D P.last Q.first) :
    (P.join Q hd he).first = P.first := by
  simp [first,join,P.nonempty]

theorem last_join (P Q : UPath D) (hd : Disjoint P.support Q.support) (he : TwoCycle D P.last Q.first) :
    (P.join Q hd he).last = Q.last := by
  simp [last,join,Q.nonempty]

def HasEdge (P : UPath D) (u v : V) : Prop :=
  ∃ l r, P.vertices = l ++ u :: v :: r ∨ P.vertices = l ++ v :: u :: r

theorem edge_reverse (P : UPath D) (u v : V) (h : P.HasEdge u v) : P.reverse.HasEdge u v := by
  obtain ⟨l,r,h | h⟩ := h
  · refine ⟨r.reverse,l.reverse,Or.inr ?_⟩
    simp [reverse,h,List.reverse_append,List.append_assoc]
  · refine ⟨r.reverse,l.reverse,Or.inl ?_⟩
    simp [reverse,h,List.reverse_append,List.append_assoc]

theorem edge_join_left (P Q : UPath D) (hd : Disjoint P.support Q.support) (he : TwoCycle D P.last Q.first)
    (u v : V) (h : P.HasEdge u v) : (P.join Q hd he).HasEdge u v := by
  obtain ⟨l,r,h | h⟩ := h
  · exact ⟨l,r ++ Q.vertices,Or.inl (by simp [join,h,List.append_assoc])⟩
  · exact ⟨l,r ++ Q.vertices,Or.inr (by simp [join,h,List.append_assoc])⟩

theorem edge_join_right (P Q : UPath D) (hd : Disjoint P.support Q.support) (he : TwoCycle D P.last Q.first)
    (u v : V) (h : Q.HasEdge u v) : (P.join Q hd he).HasEdge u v := by
  obtain ⟨l,r,h | h⟩ := h
  · exact ⟨P.vertices ++ l,r,Or.inl (by simp [join,h,List.append_assoc])⟩
  · exact ⟨P.vertices ++ l,r,Or.inr (by simp [join,h,List.append_assoc])⟩

end UPath
end ChvatalErdos

#print axioms ChvatalErdos.UPath.join
#print axioms ChvatalErdos.UPath.edge_reverse
