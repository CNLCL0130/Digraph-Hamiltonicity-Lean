import ChvatalErdos.CyclePacking
import ChvatalErdos.CycleChoice
import ChvatalErdos.DirectedPaths
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace ChvatalErdos
namespace UCycle
open CycleEndpoints
variable {V : Type} [DecidableEq V] {D : Digraph V} {b : Nat}

def rotated (Q : UCycle D b) (i t : Fin b) : V :=
  Q.vertex (index (Nat.zero_lt_of_lt i.isLt) (t.val + i.val))

theorem rotated_injective (Q : UCycle D b) (i : Fin b) : Function.Injective (Q.rotated i) :=
  Q.injective.comp (offset_injective (Nat.zero_lt_of_lt i.isLt) i.val i.isLt)

theorem rotated_range (Q : UCycle D b) (i : Fin b) (v : V) :
    v ∈ Q.support ↔ ∃ t, Q.rotated i t = v := by
  rw [Q.mem_support]
  constructor
  · rintro ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := (offsetEquiv (Nat.zero_lt_of_lt i.isLt) i.val i.isLt).surjective t
    exact ⟨s,congrArg Q.vertex hs⟩
  · rintro ⟨t,rfl⟩
    exact ⟨_,rfl⟩

theorem rotated_edge (Q : UCycle D b) (i t : Fin b) :
    TwoCycle D (Q.rotated i t) (Q.rotated i (cyclicSucc t)) := by
  have he := Q.edge (index (Nat.zero_lt_of_lt i.isLt) (t.val+i.val))
  have hs : cyclicSucc (index (Nat.zero_lt_of_lt i.isLt) (t.val+i.val)) =
      index (Nat.zero_lt_of_lt i.isLt) ((cyclicSucc t).val+i.val) := by
    apply Fin.ext
    simp only [cyclicSucc,index,Nat.mod_add_mod]
    congr 1
    omega
  simpa only [rotated,hs] using he

theorem rotated_step (Q : UCycle D b) (i : Fin b) (t : Nat) (ht : t+1 < b) :
    TwoCycle D (Q.rotated i ⟨t,by omega⟩) (Q.rotated i ⟨t+1,ht⟩) := by
  have he := Q.rotated_edge i ⟨t,by omega⟩
  have hs : cyclicSucc (⟨t,by omega⟩ : Fin b) = ⟨t+1,ht⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt ht
  simpa only [hs] using he

/-- The path obtained by removing the two ends of the retained cycle edge. -/
def complementary (Q : UCycle D b) (hb : 4 ≤ b) (i : Fin b) : UPath D where
  vertices := List.ofFn (fun t : Fin (b-2) => Q.rotated i ⟨t.val+2,by omega⟩)
  nonempty := by
    intro h
    have hh := congrArg List.length h
    simp at hh
    omega
  nodup := List.nodup_ofFn_ofInjective (by
    intro x y h
    have he := congrArg Fin.val (Q.rotated_injective i h)
    apply Fin.ext
    simpa using he)
  chain := by
    apply List.isChain_iff_getElem.mpr
    intro t ht
    have ht' : t+1 < b-2 := by simpa using ht
    have he := Q.rotated_step i (t+2) (by omega)
    simpa only [List.getElem_ofFn,Nat.add_right_comm t 1 2] using he

def retained (Q : UCycle D b) (hb : 4 ≤ b) (i : Fin b) : UPath D where
  vertices := [Q.rotated i ⟨0,by omega⟩,Q.rotated i ⟨1,by omega⟩]
  nonempty := by simp
  nodup := by
    simp only [List.nodup_cons,List.nodup_nil,List.mem_singleton,List.not_mem_nil,not_false_eq_true,and_true]
    intro h
    have he := congrArg Fin.val (Q.rotated_injective i h)
    simp at he
  chain := by
    apply List.isChain_pair.mpr
    exact Q.rotated_step i 0 (by omega)

theorem complementary_first (Q : UCycle D b) (hb : 4 ≤ b) (i : Fin b) :
    (Q.complementary hb i).first = Q.rotated i ⟨2,by omega⟩ := by
  simp [complementary,UPath.first,List.head_ofFn]

theorem complementary_last (Q : UCycle D b) (hb : 4 ≤ b) (i : Fin b) :
    (Q.complementary hb i).last = Q.rotated i ⟨b-1,by omega⟩ := by
  simp only [complementary,UPath.last,List.getLast_ofFn]
  congr 2
  omega

theorem complementary_retained_disjoint (Q : UCycle D b) (hb : 4 ≤ b) (i : Fin b) :
    Disjoint (Q.complementary hb i).support (Q.retained hb i).support := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨t,ht⟩ := List.mem_ofFn.mp ((Q.complementary hb i).mem_support x |>.1 hx)
  have hret := (Q.retained hb i).mem_support x |>.1 hx'
  simp only [retained,List.mem_cons,List.not_mem_nil,or_false] at hret
  rcases hret with h | h
  · have hh := congrArg Fin.val (Q.rotated_injective i (ht.trans h))
    dsimp at hh
    omega
  · have hh := congrArg Fin.val (Q.rotated_injective i (ht.trans h))
    dsimp at hh
    omega

theorem complementary_retained_cover (Q : UCycle D b) (hb : 4 ≤ b) (i : Fin b) :
    (Q.complementary hb i).support ∪ (Q.retained hb i).support = Q.support := by
  ext x
  rw [Q.rotated_range i]
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp ((Q.complementary hb i).mem_support x |>.1 hx)
      exact ⟨_,rfl⟩
    · have hret := (Q.retained hb i).mem_support x |>.1 hx
      simp only [retained,List.mem_cons,List.not_mem_nil,or_false] at hret
      rcases hret with rfl | rfl <;> exact ⟨_,rfl⟩
  · rintro ⟨t,rfl⟩
    by_cases ht : t.val < 2
    · apply Finset.mem_union_right
      apply (Q.retained hb i).mem_support _ |>.2
      have hcases : t.val = 0 ∨ t.val = 1 := by omega
      rcases hcases with h | h
      · have he : t = ⟨0,by omega⟩ := Fin.ext h
        simp [retained,he]
      · have he : t = ⟨1,by omega⟩ := Fin.ext h
        simp [retained,he]
    · apply Finset.mem_union_left
      apply (Q.complementary hb i).mem_support _ |>.2
      apply List.mem_ofFn.mpr
      refine ⟨⟨t.val-2,by have := t.isLt; omega⟩,?_⟩
      apply congrArg (Q.rotated i)
      apply Fin.ext
      change t.val - 2 + 2 = t.val
      omega

def physicalPath {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : UPath D :=
  if c.1 then (Q.complementary hb c.2.1).reverse else Q.complementary hb c.2.1

theorem physical_support {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.physicalPath hb c).support = (Q.complementary hb c.2.1).support := by
  cases hc : c.1 <;> simp [physicalPath,hc,UPath.support_reverse]

theorem physical_endpoints {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.physicalPath hb c).first = Q.vertex (entrance (fromRetainedEdge hb c)) ∧
    (Q.physicalPath hb c).last = Q.vertex (exit hb (fromRetainedEdge hb c)) := by
  have hfirst := (retained_endpoints hb c).1
  have hlast := (retained_endpoints hb c).2
  rw [hfirst,hlast]
  cases hc : c.1 <;>
    simp [physicalPath,hc,UPath.first_reverse,UPath.last_reverse,
      complementary_first,complementary_last,rotated,Nat.add_comm]

/-- A directed path in the entrance-coordinate sample space used in the
probability modules. Its vertex list contains the full complementary path. -/
noncomputable def selectedPath {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : DPath D :=
  (Q.physicalPath hb ((fromRetainedEdge hb).symm c)).orient

noncomputable def selectedRetained {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) : UPath D :=
  Q.retained hb ((fromRetainedEdge hb).symm c).2.1

theorem selected_endpoints {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.selectedPath hb c).first = Q.vertex (entrance c) ∧
    (Q.selectedPath hb c).last = Q.vertex (exit hb c) := by
  have he := Q.physical_endpoints hb ((fromRetainedEdge hb).symm c)
  simpa only [Equiv.apply_symm_apply] using he

theorem selected_support {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.selectedPath hb c).support =
      (Q.complementary hb ((fromRetainedEdge hb).symm c).2.1).support := by
  exact Q.physical_support hb ((fromRetainedEdge hb).symm c)

theorem selected_disjoint {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    Disjoint (Q.selectedPath hb c).support (Q.selectedRetained hb c).support := by
  rw [selected_support]
  exact Q.complementary_retained_disjoint hb _

theorem selected_cover {l : Nat} (Q : UCycle D b) (hb : 4 ≤ b) (c : Choice b l) :
    (Q.selectedPath hb c).support ∪ (Q.selectedRetained hb c).support = Q.support := by
  rw [selected_support]
  exact Q.complementary_retained_cover hb _

end UCycle
end ChvatalErdos

#print axioms ChvatalErdos.UCycle.complementary
#print axioms ChvatalErdos.UCycle.complementary_retained_disjoint
#print axioms ChvatalErdos.UCycle.complementary_retained_cover
#print axioms ChvatalErdos.UCycle.selected_endpoints
#print axioms ChvatalErdos.UCycle.selected_cover

