import ChvatalErdos.ComplementaryPaths

set_option autoImplicit false

namespace ChvatalErdos.UCycle
open CycleEndpoints
variable {V : Type} [DecidableEq V] {D : Digraph V} {b l : Nat}

noncomputable def retainedTail (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : V :=
  Q.rotated ((fromRetainedEdge hb).symm c).2.1 ⟨0,by omega⟩
noncomputable def retainedHead (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : V :=
  Q.rotated ((fromRetainedEdge hb).symm c).2.1 ⟨1,by omega⟩
noncomputable def insertForward (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : DPath D :=
  (Q.complementary hb ((fromRetainedEdge hb).symm c).2.1).reverse.orient
noncomputable def insertBackward (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : DPath D :=
  (Q.complementary hb ((fromRetainedEdge hb).symm c).2.1).orient

theorem insertion_support (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.insertForward hb c).support = (Q.selectedPath hb c).support ∧
    (Q.insertBackward hb c).support = (Q.selectedPath hb c).support := by
  rw [Q.selected_support hb c]
  exact ⟨UPath.support_reverse _,rfl⟩

theorem retained_hasEdge (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.selectedRetained hb c).HasEdge (Q.retainedTail hb c) (Q.retainedHead hb c) :=
  ⟨[],[],Or.inl rfl⟩

theorem retained_end_mem (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    Q.retainedTail hb c ∈ Q.support ∧ Q.retainedHead hb c ∈ Q.support := by
  constructor <;> apply (Q.mem_support _).2 <;> exact ⟨_,rfl⟩

theorem insertion_links (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    D.arc (Q.retainedTail hb c) (Q.insertForward hb c).first ∧
    D.arc (Q.insertForward hb c).last (Q.retainedHead hb c) ∧
    D.arc (Q.retainedHead hb c) (Q.insertBackward hb c).first ∧
    D.arc (Q.insertBackward hb c).last (Q.retainedTail hb c) := by
  let i := ((fromRetainedEdge hb).symm c).2.1
  have hnext := Q.rotated_step i 1 (by omega)
  have hclose := Q.rotated_edge i ⟨b-1,by omega⟩
  have hs : cyclicSucc (⟨b-1,by omega⟩ : Fin b) = ⟨0,by omega⟩ := by
    apply Fin.ext
    simp only [cyclicSucc]
    have he : b-1+1 = b := by omega
    simp [he]
  rw [hs] at hclose
  change D.arc (Q.rotated i _) (Q.complementary hb i).reverse.first ∧
    D.arc (Q.complementary hb i).reverse.last (Q.rotated i _) ∧
    D.arc (Q.rotated i _) (Q.complementary hb i).first ∧
    D.arc (Q.complementary hb i).last (Q.rotated i _)
  rw [UPath.first_reverse,UPath.last_reverse,Q.complementary_first,Q.complementary_last]
  exact ⟨hclose.2,hnext.2,hnext.1,hclose.1⟩

end ChvatalErdos.UCycle

#print axioms ChvatalErdos.UCycle.insertion_links
