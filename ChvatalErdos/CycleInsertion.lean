import ChvatalErdos.DirectedCycles
import ChvatalErdos.PathArcSplit

set_option autoImplicit false

namespace ChvatalErdos
namespace DCycle
variable {V : Type} [DecidableEq V] {D : Digraph V}

def HasArc (C : DCycle D) (u v : V) : Prop :=
  C.path.HasArc u v ∨ (u = C.path.last ∧ v = C.path.first)

theorem arc_of_hasArc (C : DCycle D) {u v : V} (h : C.HasArc u v) : D.arc u v := by
  rcases h with ⟨l,r,he⟩ | ⟨rfl,rfl⟩
  · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp C.path.chain he
  · exact C.closing

def close_paths (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) (hc : D.arc Q.last P.first) : DCycle D where
  path := P.join Q hd he
  closing := by simpa only [DPath.last_join,DPath.first_join] using hc

theorem close_paths_arcs (P Q : DPath D) (hd : Disjoint P.support Q.support)
    (he : D.arc P.last Q.first) (hc : D.arc Q.last P.first) (u v : V) :
    (close_paths P Q hd he hc).HasArc u v ↔
      P.HasArc u v ∨ Q.HasArc u v ∨ (u = P.last ∧ v = Q.first) ∨
      (u = Q.last ∧ v = P.first) := by
  simp only [HasArc,close_paths,DPath.arc_join_iff,DPath.last_join,DPath.first_join,or_assoc]

/-- Change the cut in a cyclic list without changing any cycle arc. -/
theorem cut_at_arc (C : DCycle D) (u v : V) (h : C.HasArc u v) :
    ∃ C' : DCycle D, C'.path.support = C.path.support ∧
      C'.path.last = u ∧ C'.path.first = v ∧
      ∀ x y, C'.HasArc x y ↔ C.HasArc x y := by
  rcases h with h | ⟨hu,hv⟩
  · obtain ⟨A,B,hvtx,hdis,hfirst,hlast,hu,hv⟩ := C.path.split_at_arc u v h
    have hab : D.arc A.last B.first := by
      rw [hu,hv]
      exact C.arc_of_hasArc (Or.inl h)
    have hba : D.arc B.last A.first := by rw [hlast,hfirst]; exact C.closing
    let C' := close_paths B A hdis.symm hba hab
    have hP : ∀ x y, C.path.HasArc x y ↔ (A.join B hdis hab).HasArc x y := by
      intro x y
      simp only [DPath.HasArc,DPath.join,hvtx]
    refine ⟨C',?_,?_,?_,?_⟩
    · ext x
      simp [C',close_paths,DPath.support,DPath.join,hvtx,or_comm]
    · simpa only [C',close_paths,DPath.last_join] using hu
    · simpa only [C',close_paths,DPath.first_join] using hv
    · intro x y
      rw [show C' = close_paths B A hdis.symm hba hab from rfl,close_paths_arcs]
      change _ ↔ C.path.HasArc x y ∨ (x = C.path.last ∧ y = C.path.first)
      rw [hP,DPath.arc_join_iff,← hlast,← hfirst]
      simp only [or_assoc,or_left_comm,or_comm]
  · exact ⟨C,rfl,hu.symm,hv.symm,fun _ _ => Iff.rfl⟩

/-- Replace a cycle arc by a disjoint nonempty path. All other old cycle arcs
remain, and the new vertex set is exactly the old set together with that path. -/
theorem insert_path (C : DCycle D) (u v : V) (h : C.HasArc u v) (Q : DPath D)
    (hd : Disjoint C.path.support Q.support) (hin : D.arc u Q.first) (hout : D.arc Q.last v) :
    ∃ C' : DCycle D, C'.path.support = C.path.support ∪ Q.support ∧
      (∀ x y, C.HasArc x y → (x,y) ≠ (u,v) → C'.HasArc x y) ∧
      Q.vertices.IsInfix C'.path.vertices := by
  obtain ⟨R,hs,hl,hf,harcs⟩ := C.cut_at_arc u v h
  have hd' : Disjoint R.path.support Q.support := by simpa only [hs] using hd
  have hin' : D.arc R.path.last Q.first := by simpa only [hl] using hin
  have hout' : D.arc Q.last R.path.first := by simpa only [hf] using hout
  let C' := close_paths R.path Q hd' hin' hout'
  refine ⟨C',?_,?_,?_⟩
  · simp only [C',close_paths,DPath.support_join,hs]
  · intro x y hxy hne
    have hrxy := (harcs x y).2 hxy
    rcases hrxy with hp | ⟨hx,hy⟩
    · apply (close_paths_arcs R.path Q hd' hin' hout' x y).2
      exact Or.inl hp
    · exact (hne (Prod.ext (hx.trans hl) (hy.trans hf))).elim
  · change Q.vertices.IsInfix (R.path.vertices ++ Q.vertices)
    exact (List.suffix_append _ _).isInfix

/-- Insert a finite family of disjoint paths along distinct retained arcs. -/
theorem insert_family {I : Type} [DecidableEq I] (C : DCycle D) (s : Finset I)
    (Q : I → DPath D) (u v : I → V)
    (harc : ∀ i ∈ s, C.HasArc (u i) (v i))
    (havoid : ∀ i ∈ s, Disjoint C.path.support (Q i).support)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Q i).support (Q j).support)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, (u i,v i) = (u j,v j) → i = j)
    (hin : ∀ i ∈ s, D.arc (u i) (Q i).first)
    (hout : ∀ i ∈ s, D.arc (Q i).last (v i)) :
    ∃ C' : DCycle D, C'.path.support = C.path.support ∪ s.biUnion (fun i => (Q i).support) ∧
      ∀ x y, C.HasArc x y → (∀ i ∈ s, (x,y) ≠ (u i,v i)) → C'.HasArc x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨C,by simp,?_⟩
    exact fun _ _ h _ => h
  | @insert a s ha ih =>
    have hsub : s ⊆ insert a s := Finset.subset_insert _ _
    obtain ⟨R,hR,hkeep⟩ := ih
      (fun i hi => harc i (hsub hi))
      (fun i hi => havoid i (hsub hi))
      (fun i hi j hj => hdis i (hsub hi) j (hsub hj))
      (fun i hi j hj => hdistinct i (hsub hi) j (hsub hj))
      (fun i hi => hin i (hsub hi)) (fun i hi => hout i (hsub hi))
    have hRa : R.HasArc (u a) (v a) := by
      apply hkeep _ _ (harc a (Finset.mem_insert_self _ _))
      intro i hi heq
      have hai := hdistinct a (Finset.mem_insert_self _ _) i (hsub hi) heq
      exact ha (hai ▸ hi)
    have hdisR : Disjoint R.path.support (Q a).support := by
      rw [hR]
      apply Finset.disjoint_union_left.mpr
      refine ⟨havoid a (Finset.mem_insert_self _ _),?_⟩
      apply Finset.disjoint_left.mpr
      intro x hx hxa
      obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
      have hia : i ≠ a := fun he => ha (he ▸ hi)
      exact Finset.disjoint_left.mp
        (hdis i (hsub hi) a (Finset.mem_insert_self _ _) hia) hxi hxa
    obtain ⟨T,hT,hTkeep,_⟩ := R.insert_path (u a) (v a) hRa (Q a) hdisR
      (hin a (Finset.mem_insert_self _ _)) (hout a (Finset.mem_insert_self _ _))
    refine ⟨T,?_,?_⟩
    · rw [hT,hR,Finset.biUnion_insert]
      ext x
      simp only [Finset.mem_union,or_assoc,or_left_comm,or_comm]
    · intro x y hxy hne
      apply hTkeep x y (hkeep x y hxy (fun i hi => hne i (hsub hi)))
      exact hne a (Finset.mem_insert_self _ _)

end DCycle

theorem hamiltonian_by_insertions {n : Nat} {D : Digraph (Fin n)}
    {I : Type} [DecidableEq I] (C : DCycle D) (s : Finset I)
    (Q : I → DPath D) (u v : I → Fin n)
    (harc : ∀ i ∈ s, C.HasArc (u i) (v i))
    (havoid : ∀ i ∈ s, Disjoint C.path.support (Q i).support)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Q i).support (Q j).support)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, (u i,v i) = (u j,v j) → i = j)
    (hin : ∀ i ∈ s, D.arc (u i) (Q i).first)
    (hout : ∀ i ∈ s, D.arc (Q i).last (v i))
    (hspan : ∀ x, x ∈ C.path.support ∪ s.biUnion (fun i => (Q i).support)) :
    Hamiltonian D := by
  obtain ⟨C',hs,_⟩ := C.insert_family s Q u v harc havoid hdis hdistinct hin hout
  apply hamiltonian_of_spanning_cycle C'
  intro x
  rw [hs]
  exact hspan x

end ChvatalErdos

#print axioms ChvatalErdos.DCycle.cut_at_arc
#print axioms ChvatalErdos.DCycle.insert_path
#print axioms ChvatalErdos.DCycle.insert_family
#print axioms ChvatalErdos.hamiltonian_by_insertions
