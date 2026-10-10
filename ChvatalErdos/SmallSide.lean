import ChvatalErdos.NeighbourObstruction
import ChvatalErdos.PackingCoordinates

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints FiniteProbability
variable {n m b l a K : Nat}

theorem predicate_count_in_complement (P : Fin n → Prop) (C U : Finset (Fin n))
    (hcover : C ∪ U = Finset.univ) (hdegree : K ≤ (Finset.univ.filter P).card)
    (hsmall : (C.card : ℝ) ≤ (K : ℝ)/2) : (K : ℝ)/2 ≤ ((U.filter P).card : ℝ) := by
  have hsub : Finset.univ.filter P ⊆ C ∪ U.filter P := by
    intro z hz
    have hzin : z ∈ C ∪ U := by rw [hcover]; exact Finset.mem_univ z
    rcases Finset.mem_union.mp hzin with hc | hu
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,(Finset.mem_filter.mp hz).2⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le C (U.filter P))
  have hh : (K : ℝ) ≤ (C.card : ℝ) + ((U.filter P).card : ℝ) := by exact_mod_cast hdegree.trans hc
  linarith

theorem small_side_neighbour_count (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hD : KStrong D K) (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (s : State n m) (hn : mixed D Q s = ∅)
    (outgoing : Bool)
    (hsmall : ((observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card : ℝ) ≤ (K : ℝ)/2)
    (z : Fin n) :
    (K : ℝ)/2 ≤ ∑ i, ((neighbourCoordinates D Q outgoing
      (if outgoing then pureRight D Q s else pureLeft D Q s) z i).card : ℝ) := by
  classical
  let C := observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)
  let I := if outgoing then pureRight D Q s else pureLeft D Q s
  let P := fun v => if outgoing then D.arc z v else D.arc v z
  have hCU : C ∪ verticesOf D Q I = Finset.univ := by
    have hp := normal_vertex_partition D Q hcover s hn
    cases outgoing
    · simpa [C,I,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using hp
    · exact hp
  have hd : K ≤ (Finset.univ.filter P).card := by
    cases outgoing
    · exact kStrong_indegree D hD z
    · exact kStrong_outdegree D hD z
  have hc := predicate_count_in_complement P C (verticesOf D Q I) hCU (by
    convert hd using 1
    congr 1
    ext v
    simp) hsmall
  have hsum : (∑ i, ((neighbourCoordinates D Q outgoing I z i).card : ℝ)) =
      (((verticesOf D Q I).filter P).card : ℝ) := by
    have he := coordinate_count D Q hdis I P
    have heR := congrArg (fun q : Nat => (q : ℝ)) he
    push_cast at heR
    convert heR using 1
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ I <;> simp [neighbourCoordinates,hi,P]
      congr 1
      ext t
      simp
    · congr 1
      congr 1
      ext v
      simp
  change (K : ℝ)/2 ≤ ∑ i, ((neighbourCoordinates D Q outgoing I z i).card : ℝ)
  rw [hsum]
  convert hc using 1
  congr 1
  congr 1
  ext v
  simp

theorem stopped_small_side_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l) (hD : KStrong D K)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (s : State n m) (hs : Supported D Q s) (hn : mixed D Q s = ∅) (outgoing : Bool)
    (T : QueryTree (Fin m) (Choice b l)) (fixed : Fin m → Choice b l)
    (hseen : s.seen = T.exposed fixed) (hbudget : (a : ℝ) ≤ (K : ℝ)/(4*b*l))
    (hsmall : ((observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card : ℝ) ≤ (K : ℝ)/2) :
    prob (compatibleEvent D Q hb a j s ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤
      (K : ℝ)*Real.exp (-(K : ℝ)/(16*b*l)) := by
  apply stopped_neighbour_obstruction_tail D Q hb hl j hdis s hs hn outgoing T fixed hseen K hbudget
  · intro z _
    exact small_side_neighbour_count D Q hD hdis hcover s hn outgoing hsmall z
  · have hk0 := Nat.cast_nonneg (α := ℝ) K
    linarith

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.stopped_small_side_tail
