import ChvatalErdos.ChordedCycle
import ChvatalErdos.DegreeCoreSubset
import ChvatalErdos.BipartiteCut

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n k : Nat}

def ChordedCycle.IsBipartite {D : Digraph (Fin n)} (C : ChordedCycle D k) (colour : Fin n → Bool) : Prop :=
  (∀ i, colour (C.cycle.vertex i) ≠ colour (C.cycle.vertex (cyclicSucc i))) ∧
    colour (C.cycle.vertex ⟨0,C.positive⟩) ≠ colour (C.cycle.vertex C.chord)

def ChordedCycle.forgetCut {D : Digraph (Fin n)} {colour : Fin n → Bool}
    (C : ChordedCycle (bipartiteCut D colour) k) : ChordedCycle D k where
  length := C.length
  positive := C.positive
  long := C.long
  cycle := ⟨C.cycle.vertex,C.cycle.injective,fun i => ⟨(C.cycle.edge i).1.1,(C.cycle.edge i).2.1⟩⟩
  chord := C.chord
  chord_low := C.chord_low
  chord_high := C.chord_high
  chord_edge := ⟨C.chord_edge.1.1,C.chord_edge.2.1⟩

theorem bipartite_chorded_of_mass (D : Digraph (Fin n)) (U : Finset (Fin n))
    (hk : 3 ≤ k) (colour : Fin n → Bool)
    (hcol : ∀ u v, TwoCycle D u v → colour u ≠ colour v)
    (hmass : 2*((k : ℝ)-1)*U.card < edgeMass D U) :
    ∃ C : ChordedCycle D k, C.cycle.support ⊆ U := by
  have hU : U.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [he,edgeMass] at hmass
  have hcard : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
  let δ := edgeMass D U/(2*U.card)
  have hδk : (k : ℝ)-1 < δ := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*U.card)).2
    nlinarith [hmass]
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hδ : 0 < δ := by linarith
  have hstart : 2*δ*U.card ≤ edgeMass D U := by
    have heq : 2*δ*U.card = edgeMass D U := by dsimp [δ]; field_simp
    exact heq.le
  obtain ⟨V,hVU,hV,hdeg⟩ := exists_degree_core_subset D U hU δ hδ hstart
  have hdegK : ∀ v ∈ V, (k : ℝ) ≤ degreeMass D V v := by
    intro v hv
    have hd := hdeg v hv
    have he : degreeMass D V v = ((V.filter (fun w => TwoCycle D v w)).card : ℝ) := by simp [degreeMass]
    rw [he] at hd ⊢
    have hn : k ≤ (V.filter (fun w => TwoCycle D v w)).card := by
      by_contra hn
      have hh : (V.filter (fun w => TwoCycle D v w)).card+1 ≤ k := by omega
      have hhR : ((V.filter (fun w => TwoCycle D v w)).card : ℝ)+1 ≤ k := by exact_mod_cast hh
      linarith
    exact_mod_cast hn
  obtain ⟨C,hC⟩ := bipartite_min_degree_chorded D V hV hk colour hcol hdegK
  exact ⟨C,hC.trans hVU⟩

theorem bipartite_mass_of_no_chorded (D : Digraph (Fin n)) (U : Finset (Fin n))
    (hk : 3 ≤ k) (colour : Fin n → Bool)
    (hcol : ∀ u v, TwoCycle D u v → colour u ≠ colour v)
    (hno : ∀ C : ChordedCycle D k, ¬C.cycle.support ⊆ U) :
    edgeMass D U ≤ 2*((k : ℝ)-1)*U.card := by
  by_contra h
  obtain ⟨C,hC⟩ := bipartite_chorded_of_mass D U hk colour hcol (lt_of_not_ge h)
  exact hno C hC

theorem mass_of_no_bipartite_chorded (D : Digraph (Fin n)) (U : Finset (Fin n))
    (hk : 3 ≤ k)
    (hno : ∀ C : ChordedCycle D k, C.cycle.support ⊆ U → ∀ colour, ¬C.IsBipartite colour) :
    edgeMass D U ≤ 4*((k : ℝ)-1)*U.card := by
  by_contra h
  obtain ⟨colour,hcut⟩ := exists_bipartiteCut_half D U
  have hmass : 2*((k : ℝ)-1)*U.card < edgeMass (bipartiteCut D colour) U := by linarith
  obtain ⟨C,hC⟩ := bipartite_chorded_of_mass (bipartiteCut D colour) U hk colour (fun _ _ h => h.1.2) hmass
  apply hno C.forgetCut hC colour
  exact ⟨fun i => (C.cycle.edge i).1.2,C.chord_edge.1.2⟩

end ChvatalErdos

#print axioms ChvatalErdos.bipartite_mass_of_no_chorded
#print axioms ChvatalErdos.mass_of_no_bipartite_chorded
