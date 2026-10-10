import ChvatalErdos.NormalRecords
import ChvatalErdos.StoppedNeighbours
import ChvatalErdos.MatchingObstruction
import ChvatalErdos.ConditionalUnion

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints FiniteProbability
variable {n m b l a : Nat}

noncomputable def neighbourCoordinates (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (outgoing : Bool) (I : Finset (Fin m)) (z : Fin n) (i : Fin m) : Finset (Fin b) :=
  if i ∈ I then Finset.univ.filter (fun t => if outgoing then D.arc z ((Q i).vertex t) else D.arc ((Q i).vertex t) z)
  else ∅

noncomputable def neighbourIndices (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (outgoing : Bool) (I : Finset (Fin m)) (j : Fin l) (z : Fin n)
    (x : Fin m → Choice b l) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i ∈ I ∧ colour (x i) = j ∧
    if outgoing then D.arc z ((Q i).vertex (entrance (x i))) else D.arc ((Q i).vertex (exit hb (x i))) z)

theorem neighbour_count_eq_card (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (outgoing : Bool) (I : Finset (Fin m)) (j : Fin l) (z : Fin n)
    (x : Fin m → Choice b l) :
    successCount (fun i => directedNeighbourEvent hb outgoing (neighbourCoordinates D Q outgoing I z i) j) x =
      ((neighbourIndices D Q hb outgoing I j z x).card : ℝ) := by
  have hi : ∀ i, x i ∈ directedNeighbourEvent hb outgoing (neighbourCoordinates D Q outgoing I z i) j ↔
      i ∈ neighbourIndices D Q hb outgoing I j z x := by
    intro i
    cases outgoing <;> by_cases h : i ∈ I <;>
      simp [directedNeighbourEvent,neighbourCoordinates,neighbourIndices,neighbourEvent,exitNeighbourEvent,h,and_comm,and_left_comm]
  simp only [successCount,hi]
  simp

theorem Separation.out_neighbours_small (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (j : Fin l) (x : Fin m → Choice b l) (S : Separation D Q hb a j x)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hc : S.Compatible s) (i : Fin m) (hi : i ∈ S.L) :
    (neighbourIndices D Q hb true (pureRight D Q s) j ((Q i).vertex (exit hb (x i))) x).card < a := by
  have hsub : neighbourIndices D Q hb true (pureRight D Q s) j ((Q i).vertex (exit hb (x i))) x ⊆ S.X := by
    intro k hk
    have ht := (Finset.mem_filter.mp hk).2
    have hp := (Finset.mem_filter.mp ht.1).2
    rcases S.pure_right_forced hdis s hs hc k hp.1 hp.2 ht.2.1 with hr | hx
    · exact (S.no_arc i hi k hr ht.2.2).elim
    · exact hx
  exact lt_of_le_of_lt (Finset.card_le_card hsub) S.small

theorem Separation.in_neighbours_small (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (j : Fin l) (x : Fin m → Choice b l) (S : Separation D Q hb a j x)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hc : S.Compatible s) (i : Fin m) (hi : i ∈ S.R) :
    (neighbourIndices D Q hb false (pureLeft D Q s) j ((Q i).vertex (entrance (x i))) x).card < a := by
  have hsub : neighbourIndices D Q hb false (pureLeft D Q s) j ((Q i).vertex (entrance (x i))) x ⊆ S.X := by
    intro k hk
    have ht := (Finset.mem_filter.mp hk).2
    have hp := (Finset.mem_filter.mp ht.1).2
    rcases S.pure_left_forced hdis s hs hc k hp.1 hp.2 ht.2.1 with hl | hx
    · exact (S.no_arc k hl i hi ht.2.2).elim
    · exact hx
  exact lt_of_le_of_lt (Finset.card_le_card hsub) S.small

theorem Separation.exists_low_neighbour_count (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (j : Fin l) (x : Fin m → Choice b l) (S : Separation D Q hb a j x)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hc : S.Compatible s) (hn : mixed D Q s = ∅)
    (outgoing : Bool) :
    ∃ z ∈ observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s),
      successCount (fun i => directedNeighbourEvent hb outgoing
        (neighbourCoordinates D Q outgoing (if outgoing then pureRight D Q s else pureLeft D Q s) z i) j) x < (a : ℝ) := by
  cases outgoing with
  | true =>
    obtain ⟨i,hi⟩ := S.left_nonempty
    refine ⟨(Q i).vertex (exit hb (x i)),S.left_exit_location D Q hb j x hdis s hs hc hn i hi,?_⟩
    rw [neighbour_count_eq_card]
    exact_mod_cast S.out_neighbours_small D Q hb j x hdis s hs hc i hi
  | false =>
    obtain ⟨i,hi⟩ := S.right_nonempty
    refine ⟨(Q i).vertex (entrance (x i)),S.right_entrance_location D Q hb j x hdis s hs hc hn i hi,?_⟩
    rw [neighbour_count_eq_card]
    exact_mod_cast S.in_neighbours_small D Q hb j x hdis s hs hc i hi

theorem stopped_neighbour_obstruction_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hn : mixed D Q s = ∅) (outgoing : Bool)
    (T : QueryTree (Fin m) (Choice b l)) (fixed : Fin m → Choice b l)
    (hseen : s.seen = T.exposed fixed) (K : ℝ)
    (hbudget : (a : ℝ) ≤ K/(4*b*l))
    (hcount : ∀ z ∈ observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s),
      K/2 ≤ ∑ i, ((neighbourCoordinates D Q outgoing
        (if outgoing then pureRight D Q s else pureLeft D Q s) z i).card : ℝ))
    (hcard : ((observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card : ℝ) ≤ K) :
    prob (compatibleEvent D Q hb a j s ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤
      K*Real.exp (-K/(16*b*l)) := by
  let C := observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)
  let I := if outgoing then pureRight D Q s else pureLeft D Q s
  let B := fun z i => neighbourCoordinates D Q outgoing I z i
  let events := fun z => Finset.univ.filter (fun x : Fin m → Choice b l =>
    successCount (fun i => directedNeighbourEvent hb outgoing (B z i) j) x < (a : ℝ))
  have hcover : ∀ x ∈ compatibleEvent D Q hb a j s ∩ historyEvent T fixed, ∃ z ∈ C, x ∈ events z := by
    intro x hx
    obtain ⟨S,hS⟩ := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
    obtain ⟨z,hz,hzcount⟩ := S.exists_low_neighbour_count D Q hb j x hdis s hs hS hn outgoing
    exact ⟨z,hz,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzcount⟩⟩
  have hbound : ∀ z ∈ C, prob (events z ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤
      Real.exp (-K/(16*b*l)) := by
    intro z hz
    apply stopped_neighbour_tail hb hl outgoing (B z) j T fixed _ K a (hcount z hz) hbudget
    intro i hi
    have his : i ∈ s.seen := hseen ▸ hi
    have hnot : i ∉ I := by
      dsimp [I]
      cases outgoing <;> simp only [Bool.false_eq_true,if_false,if_true]
      · intro hh; exact (Finset.mem_filter.mp hh).2.1 his
      · intro hh; exact (Finset.mem_filter.mp hh).2.1 his
    simp [B,neighbourCoordinates,hnot]
  exact (conditional_union_bound _ _ C events hcover _ hbound).trans
    (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.Separation.exists_low_neighbour_count
#print axioms ChvatalErdos.Record.stopped_neighbour_obstruction_tail
