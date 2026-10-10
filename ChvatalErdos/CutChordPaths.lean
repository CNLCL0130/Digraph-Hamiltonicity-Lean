import ChvatalErdos.ChordedDensity
import ChvatalErdos.ChordPathLemma
import ChvatalErdos.PathInterval
import ChvatalErdos.GraphEmbedding

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n k : Nat} {D : Digraph (Fin n)}

def ChordedCycle.toCut (C : ChordedCycle D k) (colour : Fin n → Bool) (hC : C.IsBipartite colour) :
    ChordedCycle (bipartiteCut D colour) k where
  length := C.length
  positive := C.positive
  long := C.long
  cycle := ⟨C.cycle.vertex,C.cycle.injective,fun i =>
    ⟨⟨(C.cycle.edge i).1,hC.1 i⟩,⟨(C.cycle.edge i).2,(hC.1 i).symm⟩⟩⟩
  chord := C.chord
  chord_low := C.chord_low
  chord_high := C.chord_high
  chord_edge := ⟨⟨C.chord_edge.1,hC.2⟩,⟨C.chord_edge.2,hC.2.symm⟩⟩

theorem ChordedCycle.path_across_part (C : ChordedCycle D k) (colour : Fin n → Bool)
    (hC : C.IsBipartite colour) (c : Bool) (A : Finset (Fin n))
    (hA : A ⊆ C.cycle.support.filter (fun v => colour v = c)) (ha : A.Nonempty)
    (hb : ((C.cycle.support.filter (fun v => colour v = c)) \ A).Nonempty)
    (L : Nat) (hL : 0 < L) (hLb : L < C.length) (heven : L%2 = 0) :
    ∃ P : UPath D, P.support ⊆ C.cycle.support ∧ P.vertices.length = L+1 ∧
      P.first ∈ A ∧ P.last ∈ (C.cycle.support.filter (fun v => colour v = c)) \ A := by
  let C' := C.toCut colour hC
  let splitColour := fun v => decide (v ∈ A)
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  have haS := (Finset.mem_filter.mp (hA ha)).1
  have hbS := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).1
  have hbc := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
  have hbA := (Finset.mem_sdiff.mp hb).2
  obtain ⟨ia,hia⟩ := (C.cycle.mem_support a).mp haS
  obtain ⟨ib,hib⟩ := (C.cycle.mem_support b).mp hbS
  have hne : ∃ i j, splitColour (C'.cycle.vertex i) ≠ splitColour (C'.cycle.vertex j) := by
    refine ⟨ia,ib,?_⟩
    change decide (C.cycle.vertex ia ∈ A) ≠ decide (C.cycle.vertex ib ∈ A)
    simp [hia,hib,ha,hbA]
  have hbad : ∃ i, splitColour (C'.cycle.vertex i) = splitColour (C'.cycle.vertex (cyclicSucc i)) := by
    refine ⟨ib,?_⟩
    have hsucc : C.cycle.vertex (cyclicSucc ib) ∉ A := by
      intro hs
      have hc := (Finset.mem_filter.mp (hA hs)).2
      have hh := hC.1 ib
      rw [hib,hbc,hc] at hh
      exact hh rfl
    change decide (C.cycle.vertex ib ∈ A) = decide (C.cycle.vertex (cyclicSucc ib) ∈ A)
    simp [hib,hbA,hsucc]
  obtain ⟨P,hPS,hlen,hends⟩ := chord_crossing_path C'.cycle C'.positive C'.chord C'.chord_low
    C'.chord_high C'.chord_edge splitColour hne hbad L hL hLb
  have hex : ∃ Q : UPath (bipartiteCut D colour), Q.support ⊆ C'.cycle.support ∧
      Q.vertices.length = L+1 ∧ Q.first ∈ A ∧ Q.last ∉ A := by
    by_cases hfirst : P.first ∈ A
    · refine ⟨P,hPS,hlen,hfirst,?_⟩
      intro hlast
      apply hends
      simp [splitColour,hfirst,hlast]
    · refine ⟨P.reverse,?_,?_,?_,?_⟩
      · simpa only [UPath.support_reverse] using hPS
      · simpa only [UPath.reverse,List.length_reverse] using hlen
      · rw [UPath.first_reverse]
        by_contra hlast
        apply hends
        simp [splitColour,hfirst,hlast]
      · simpa only [UPath.last_reverse] using hfirst
  obtain ⟨Q,hQS,hQlen,hQfirst,hQlast⟩ := hex
  have hsame : colour Q.first = colour Q.last := Q.even_length_same_colour colour
    (fun _ _ he => he.1.2) (by simpa only [hQlen,Nat.add_sub_cancel] using heven)
  have hlastColour : colour Q.last = c := hsame.symm.trans (Finset.mem_filter.mp (hA hQfirst)).2
  let e : GraphEmbedding (bipartiteCut D colour) D := ⟨id,Function.injective_id,fun _ _ h => h.1⟩
  have hsupport : (Q.mapGraph e).support = Q.support := by simp [UPath.support_mapGraph,e]
  refine ⟨Q.mapGraph e,?_,?_,?_,?_⟩
  · rw [hsupport]; exact hQS
  · simpa only [UPath.mapGraph,List.length_map] using hQlen
  · simpa only [UPath.first_mapGraph] using hQfirst
  · rw [UPath.last_mapGraph]
    change Q.last ∈ (C.cycle.support.filter (fun v => colour v = c)) \ A
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact hQS Q.last_mem
      · exact hlastColour
    · exact hQlast

end ChvatalErdos

#print axioms ChvatalErdos.ChordedCycle.path_across_part
