import ChvatalErdos.MatchingObstruction
import ChvatalErdos.PackingCoordinates
import ChvatalErdos.InducedCutMatching

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints FiniteProbability
variable {n m b l a K q : Nat}

theorem normal_pure_vertex_partition (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (s : State n m) (hn : mixed D Q s = ∅) :
    verticesOf D Q (pureLeft D Q s) ∪ verticesOf D Q (pureRight D Q s) = Finset.univ \ observed D Q s := by
  have hl : Disjoint s.seen (pureLeft D Q s) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact (Finset.mem_filter.mp hi').2.1 hi
  have hr : Disjoint s.seen (pureRight D Q s) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact (Finset.mem_filter.mp hi').2.1 hi
  have hdL := verticesOf_disjoint D Q hdis s.seen (pureLeft D Q s) hl
  have hdR := verticesOf_disjoint D Q hdis s.seen (pureRight D Q s) hr
  have hp := normal_vertex_partition D Q hcover s hn
  ext z
  constructor
  · intro hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hzW
    rcases Finset.mem_union.mp hz with hzl | hzr
    · exact Finset.disjoint_left.mp hdL hzW hzl
    · exact Finset.disjoint_left.mp hdR hzW hzr
  · intro hz
    have hzall : z ∈ observed D Q s ∪ verticesOf D Q (pureLeft D Q s) ∪ verticesOf D Q (pureRight D Q s) := by
      rw [hp]; exact Finset.mem_univ _
    simp only [Finset.mem_union] at hzall ⊢
    rcases hzall with (hzw | hzl) | hzr
    · exact ((Finset.mem_sdiff.mp hz).2 hzw).elim
    · exact Or.inl hzl
    · exact Or.inr hzr

theorem stopped_large_side_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l) (hD : KStrong D K)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (s : State n m) (hs : Supported D Q s) (hn : mixed D Q s = ∅)
    (hW : q+(observed D Q s).card ≤ K)
    (hleft : q ≤ (verticesOf D Q (pureLeft D Q s)).card)
    (hright : q ≤ (verticesOf D Q (pureRight D Q s)).card)
    (T : QueryTree (Fin m) (Choice b l)) (fixed : Fin m → Choice b l)
    (hseen : s.seen = T.exposed fixed) (hbudget : (a : ℝ) ≤ (q : ℝ)/(2*b^2*l^2)) :
    prob (compatibleEvent D Q hb a j s ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤
      Real.exp (-(q : ℝ)/(8*b^2*l^2)) := by
  have hD' : KStrong D (q+(observed D Q s).card) := by
    refine ⟨by have hd := hD.1; omega,?_⟩
    intro S hS hc
    exact hD.2 S hS (lt_of_lt_of_le hc hW)
  have hstrong := kStrong_delete D hD' (observed D Q s) (le_refl _)
  have hd := verticesOf_disjoint D Q hdis _ _ (pure_disjoint D Q (by omega) s)
  obtain ⟨u₀,v₀,hu₀,hv₀,hmatch⟩ := induced_cut_matching D _ _ _ hstrong
    (normal_pure_vertex_partition D Q hdis hcover s hn) hd (le_refl q) hleft hright
  have hexu : ∀ e : Fin q, ∃ p : Fin m × Fin b, p.1 ∈ pureLeft D Q s ∧ (Q p.1).vertex p.2 = u₀ e := by
    intro e
    obtain ⟨i,hi,hui⟩ := Finset.mem_biUnion.mp (hmatch e).1
    obtain ⟨t,ht⟩ := (Q i).mem_support _ |>.1 hui
    exact ⟨(i,t),hi,ht⟩
  have hexv : ∀ e : Fin q, ∃ p : Fin m × Fin b, p.1 ∈ pureRight D Q s ∧ (Q p.1).vertex p.2 = v₀ e := by
    intro e
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp (hmatch e).2.1
    obtain ⟨t,ht⟩ := (Q i).mem_support _ |>.1 hvi
    exact ⟨(i,t),hi,ht⟩
  choose u hu using hexu
  choose v hv using hexv
  have hui : Function.Injective u := by
    intro e f hef
    apply hu₀
    rw [← (hu e).2,← (hu f).2,hef]
  have hvi : Function.Injective v := by
    intro e f hef
    apply hv₀
    rw [← (hv e).2,← (hv f).2,hef]
  apply stopped_matching_obstruction_tail D Q hb hl j hdis s hs u v hui hvi
    (fun e => (Finset.mem_filter.mp (hu e).1).2.1)
    (fun e => (Finset.mem_filter.mp (hv e).1).2.1)
    (fun e => (Finset.mem_filter.mp (hu e).1).2.2)
    (fun e => (Finset.mem_filter.mp (hv e).1).2.2) _ T fixed hseen hbudget
  intro e
  rw [(hu e).2,(hv e).2]
  exact (hmatch e).2.2

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.stopped_large_side_tail
