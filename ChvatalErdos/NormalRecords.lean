import ChvatalErdos.RecordSeparations

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints
variable {n m b l a : Nat}

noncomputable def pureLeft (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i ∉ s.seen ∧ ∀ t, left D Q s i t)
noncomputable def pureRight (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i ∉ s.seen ∧ ∀ t, right D Q s i t)

theorem normal_partition (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m)
    (hn : mixed D Q s = ∅) (i : Fin m) :
    i ∈ s.seen ∨ i ∈ pureLeft D Q s ∨ i ∈ pureRight D Q s := by
  by_cases hi : i ∈ s.seen
  · exact Or.inl hi
  · by_cases hl : ∀ t, left D Q s i t
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hl⟩))
    · by_cases hr : ∀ t, right D Q s i t
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hr⟩))
      · have hh : i ∈ mixed D Q s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hl,hr⟩
        rw [hn] at hh
        exact (Finset.notMem_empty _ hh).elim

theorem pure_disjoint (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 0 < b) (s : State n m) :
    Disjoint (pureLeft D Q s) (pureRight D Q s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  have hl := (Finset.mem_filter.mp hi).2.2 ⟨0,hb⟩
  have hr := (Finset.mem_filter.mp hi').2.2 ⟨0,hb⟩
  exact left_right_exclusive D (· ∈ s.left) (· ∈ s.right) _ ⟨hl,hr⟩

noncomputable def verticesOf (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (I : Finset (Fin m)) : Finset (Fin n) :=
  I.biUnion (fun i => (Q i).support)

theorem vertex_in_verticesOf (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (I : Finset (Fin m)) (i : Fin m) (hi : i ∈ I) (t : Fin b) :
    (Q i).vertex t ∈ verticesOf D Q I :=
  Finset.mem_biUnion.mpr ⟨i,hi,(Q i).mem_support _ |>.2 ⟨t,rfl⟩⟩

theorem Separation.left_exit_location (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (j : Fin l) (x : Fin m → Choice b l) (S : Separation D Q hb a j x)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hc : S.Compatible s) (hn : mixed D Q s = ∅)
    (i : Fin m) (hi : i ∈ S.L) :
    (Q i).vertex (exit hb (x i)) ∈ observed D Q s ∪ verticesOf D Q (pureLeft D Q s) := by
  rcases normal_partition D Q s hn i with hi' | hi' | hi'
  · exact Finset.mem_union_left _ (vertex_in_verticesOf D Q s.seen i hi' _)
  · exact Finset.mem_union_right _ (vertex_in_verticesOf D Q _ i hi' _)
  · have ht := (Finset.mem_filter.mp hi').2
    have hcol := (S.partition i).2 (Or.inl hi)
    rcases S.pure_right_forced hdis s hs hc i ht.1 ht.2 hcol with hr | hx
    · exact (Finset.disjoint_left.mp S.left_right hi hr).elim
    · exact (Finset.disjoint_left.mp S.left_separator hi hx).elim

theorem Separation.right_entrance_location (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (j : Fin l) (x : Fin m → Choice b l) (S : Separation D Q hb a j x)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hc : S.Compatible s) (hn : mixed D Q s = ∅)
    (i : Fin m) (hi : i ∈ S.R) :
    (Q i).vertex (entrance (x i)) ∈ observed D Q s ∪ verticesOf D Q (pureRight D Q s) := by
  rcases normal_partition D Q s hn i with hi' | hi' | hi'
  · exact Finset.mem_union_left _ (vertex_in_verticesOf D Q s.seen i hi' _)
  · have ht := (Finset.mem_filter.mp hi').2
    have hcol := (S.partition i).2 (Or.inr (Or.inr hi))
    rcases S.pure_left_forced hdis s hs hc i ht.1 ht.2 hcol with hl | hx
    · exact (Finset.disjoint_left.mp S.left_right hl hi).elim
    · exact (Finset.disjoint_left.mp S.separator_right hx hi).elim
  · exact Finset.mem_union_right _ (vertex_in_verticesOf D Q _ i hi' _)

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.Separation.left_exit_location
#print axioms ChvatalErdos.Record.Separation.right_entrance_location
