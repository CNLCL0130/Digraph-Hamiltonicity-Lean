import ChvatalErdos.AncestorSplit
import ChvatalErdos.CutChordPaths
import ChvatalErdos.CycleParts
import ChvatalErdos.TwoPathsCycle

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.RootedParent
variable {n k : Nat} {D : Digraph (Fin n)} {U : Finset (Fin n)} (T : RootedParent D U)

theorem cycle_from_level_chord (C : ChordedCycle D k) (hk : 2 ≤ k)
    (colour : Fin n → Bool) (hC : C.IsBipartite colour) (c : Bool) (i : Nat)
    (hi : 0 < i) (hik : i < k) (hCU : C.cycle.support ⊆ U)
    (hmin : ∀ v ∈ C.cycle.support, i ≤ T.depth v)
    (hpart : ∀ v ∈ C.cycle.support, colour v = c → T.depth v = i) :
    Nonempty (UCycle D (2*k)) := by
  let Y := C.cycle.support.filter (fun v => colour v = c)
  have hYU : Y ⊆ U := (Finset.filter_subset _ _).trans hCU
  have hYlevel : ∀ v ∈ Y, T.depth v = i := by
    intro v hv
    exact hpart v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  have hYmany : 1 < Y.card := C.cycle.bipartite_part_many (by have h := C.long; omega) colour hC.1 c
  obtain ⟨q,A,hq,hAY,hA,hB,hpaths⟩ := T.split_level Y hYU i hYlevel hYmany
  let L := 2*k-2*(i-q)
  have hL : 0 < L := by dsimp [L]; omega
  have hLb : L < C.length := by dsimp [L]; have h := C.long; omega
  have heven : L%2 = 0 := by dsimp [L]; omega
  obtain ⟨P,hPS,hPlen,hPa,hPb⟩ := C.path_across_part colour hC c A hAY hA hB L hL hLb heven
  obtain ⟨B,hBfirst,hBlast,hBlen,hBU,hBdepth⟩ := hpaths P.first hPa P.last hPb
  have hinter : ∀ z ∈ P.support, z ∈ B.support → z = B.first ∨ z = B.last := by
    intro z hzP hzB
    have hd := hmin z (hPS hzP)
    rcases hBdepth z hzB with hh | hh | hh
    · omega
    · exact Or.inl (hh.trans hBfirst.symm)
    · exact Or.inr (hh.trans hBlast.symm)
  have hcycle := P.cycle_of_two_paths B L (2*(i-q)) hL (by omega) hPlen hBlen hBfirst.symm hBlast.symm hinter
  have hlen : L+2*(i-q) = 2*k := by dsimp [L]; omega
  rwa [hlen] at hcycle

end ChvatalErdos.RootedParent

#print axioms ChvatalErdos.RootedParent.cycle_from_level_chord
