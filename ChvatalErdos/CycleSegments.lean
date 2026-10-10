import ChvatalErdos.ComplementaryPaths

set_option autoImplicit false

namespace ChvatalErdos.UCycle
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

def segment (Q : UCycle D b) (i : Fin b) (L : Nat) (hL : L < b) : UPath D where
  vertices := List.ofFn (fun t : Fin (L+1) => Q.rotated i ⟨t.val,by omega⟩)
  nonempty := by intro h; have he := congrArg List.length h; simp at he
  nodup := List.nodup_ofFn_ofInjective (by
    intro s t hst
    exact Fin.ext (congrArg (fun w : Fin b => w.val) (Q.rotated_injective i hst)))
  chain := by
    apply List.isChain_iff_getElem.mpr
    intro t ht
    have ht' : t+1 < L+1 := by simpa using ht
    simpa only [List.getElem_ofFn] using Q.rotated_step i t (by omega)

theorem segment_length (Q : UCycle D b) (i : Fin b) (L : Nat) (hL : L < b) :
    (Q.segment i L hL).vertices.length = L+1 := by simp [segment]

theorem segment_first (Q : UCycle D b) (i : Fin b) (L : Nat) (hL : L < b) :
    (Q.segment i L hL).first = Q.vertex i := by
  simp [segment,UPath.first,List.head_ofFn,rotated,index,Nat.mod_eq_of_lt i.isLt]

theorem segment_last (Q : UCycle D b) (i : Fin b) (L : Nat) (hL : L < b) :
    (Q.segment i L hL).last = Q.vertex (index (by omega : 0 < b) (i.val+L)) := by
  simp only [segment,UPath.last,List.getLast_ofFn,rotated]
  congr 2
  simp [Nat.add_comm]

theorem segment_support (Q : UCycle D b) (i : Fin b) (L : Nat) (hL : L < b) :
    (Q.segment i L hL).support ⊆ Q.support := by
  intro v hv
  obtain ⟨t,rfl⟩ := List.mem_ofFn.mp ((Q.segment i L hL).mem_support v |>.1 hv)
  exact (Q.mem_support _).2 ⟨_,rfl⟩

theorem mem_segment (Q : UCycle D b) (i : Fin b) (L : Nat) (hL : L < b) (v : Fin n) :
    v ∈ (Q.segment i L hL).support ↔ ∃ t : Nat, t ≤ L ∧ Q.vertex (index (by omega : 0 < b) (i.val+t)) = v := by
  rw [UPath.mem_support]
  change v ∈ List.ofFn (fun t : Fin (L+1) => Q.rotated i ⟨t.val,by omega⟩) ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t.val,by omega,by simpa only [rotated,Nat.add_comm] using ht⟩
  · rintro ⟨t,ht,hv⟩
    exact ⟨⟨t,by omega⟩,by simpa only [rotated,Nat.add_comm] using hv⟩

end ChvatalErdos.UCycle

#print axioms ChvatalErdos.UCycle.segment_last
