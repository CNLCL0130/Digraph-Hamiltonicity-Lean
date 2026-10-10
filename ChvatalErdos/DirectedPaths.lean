import ChvatalErdos.Paths

set_option autoImplicit false

namespace ChvatalErdos

/-- A nonempty simple directed path, including a singleton. -/
structure DPath {V : Type} (D : Digraph V) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  chain : vertices.IsChain D.arc

namespace DPath
variable {V : Type} [DecidableEq V] {D : Digraph V}

def first (P : DPath D) : V := P.vertices.head P.nonempty
def last (P : DPath D) : V := P.vertices.getLast P.nonempty
def support (P : DPath D) : Finset V := P.vertices.toFinset

theorem mem_support (P : DPath D) (v : V) : v ∈ P.support ↔ v ∈ P.vertices := by
  simp [support]

theorem first_mem (P : DPath D) : P.first ∈ P.support :=
  (P.mem_support _).2 (List.head_mem P.nonempty)

theorem last_mem (P : DPath D) : P.last ∈ P.support :=
  (P.mem_support _).2 (List.getLast_mem P.nonempty)

def singleton (v : V) : DPath D where
  vertices := [v]
  nonempty := by simp
  nodup := by simp
  chain := by simp

def join (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) : DPath D where
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

theorem support_join (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) :
    (P.join Q hd he).support = P.support ∪ Q.support := by
  ext v
  simp [support,join]

theorem first_join (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) : (P.join Q hd he).first = P.first := by
  simp [first,join,P.nonempty]

theorem last_join (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) : (P.join Q hd he).last = Q.last := by
  simp [last,join,Q.nonempty]

def HasArc (P : DPath D) (u v : V) : Prop :=
  ∃ l r, P.vertices = l ++ u :: v :: r

theorem arc_join_left (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) (u v : V) (h : P.HasArc u v) :
    (P.join Q hd he).HasArc u v := by
  obtain ⟨l,r,h⟩ := h
  exact ⟨l,r ++ Q.vertices,by simp [join,h,List.append_assoc]⟩

theorem arc_join_right (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) (u v : V) (h : Q.HasArc u v) :
    (P.join Q hd he).HasArc u v := by
  obtain ⟨l,r,h⟩ := h
  exact ⟨P.vertices ++ l,r,by simp [join,h,List.append_assoc]⟩

theorem prefix_to (P : DPath D) (v : V) (hv : v ∈ P.support) :
    ∃ Q : DPath D, Q.first = P.first ∧ Q.last = v ∧ Q.support ⊆ P.support := by
  obtain ⟨l,r,heq⟩ := List.mem_iff_append.mp ((P.mem_support v).1 hv)
  have hsplit : P.vertices = (l ++ [v]) ++ r := by simpa [List.append_assoc] using heq
  let Q : DPath D := {
    vertices := l ++ [v]
    nonempty := by simp
    nodup := (List.nodup_append.mp (hsplit ▸ P.nodup)).1
    chain := (List.isChain_append.mp (hsplit ▸ P.chain)).1 }
  refine ⟨Q,?_,?_,?_⟩
  · simp only [first,Q]
    cases l <;> simp_all
  · simp [last,Q]
  · intro w hw
    apply (P.mem_support w).2
    rw [hsplit]
    exact List.mem_append_left _ ((Q.mem_support w).1 hw)

end DPath

def UPath.orient {V : Type} {D : Digraph V} (P : UPath D) : DPath D where
  vertices := P.vertices
  nonempty := P.nonempty
  nodup := P.nodup
  chain := P.chain.imp (fun _ _ h => h.1)

theorem UPath.orient_edge {V : Type} [DecidableEq V] {D : Digraph V}
    (P : UPath D) (u v : V) (h : P.HasEdge u v) :
    P.orient.HasArc u v ∨ P.orient.HasArc v u := by
  obtain ⟨l,r,h | h⟩ := h
  · exact Or.inl ⟨l,r,h⟩
  · exact Or.inr ⟨l,r,h⟩

/-- Loop erasure: reachability always has a simple path witness in the allowed set. -/
theorem path_of_reach {V : Type} [DecidableEq V] {D : Digraph V}
    {allowed : V → Prop} {u v : V} (h : Reach D allowed u v) :
    ∃ P : DPath D, P.first = u ∧ P.last = v ∧ ∀ w ∈ P.support, allowed w := by
  induction h with
  | refl hv =>
    refine ⟨DPath.singleton u,rfl,rfl,?_⟩
    simpa [DPath.support,DPath.singleton] using hv
  | @step v w h he hw ih =>
    obtain ⟨P,hfirst,hlast,hallowed⟩ := ih
    by_cases hmem : w ∈ P.support
    · obtain ⟨Q,hqf,hql,hsub⟩ := P.prefix_to w hmem
      exact ⟨Q,hqf.trans hfirst,hql,fun z hz => hallowed z (hsub hz)⟩
    · have hd : Disjoint P.support (DPath.singleton (D := D) w).support := by
        simpa [DPath.support,DPath.singleton] using hmem
      have he' : D.arc P.last (DPath.singleton (D := D) w).first := by
        simpa [hlast,DPath.first,DPath.singleton] using he
      refine ⟨P.join (DPath.singleton w) hd he',?_,?_,?_⟩
      · simpa only [DPath.first_join] using hfirst
      · rw [DPath.last_join]; rfl
      · intro z hz
        rw [DPath.support_join] at hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact hallowed z hz
        · have hzw : z = w := by simpa [DPath.support,DPath.singleton] using hz
          exact hzw ▸ hw

end ChvatalErdos

#print axioms ChvatalErdos.path_of_reach
#print axioms ChvatalErdos.UPath.orient_edge

