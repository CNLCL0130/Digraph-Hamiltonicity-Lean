import ChvatalErdos.ShortChord
import ChvatalErdos.FarChord
import ChvatalErdos.CycleRotate

set_option autoImplicit false

namespace ChvatalErdos
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

theorem chord_no_crossing_bipartition (Q : UCycle D b) (hb : 0 < b) (r : Fin b)
    (hrlo : 1 < r.val) (hrhi : r.val+1 < b)
    (he : TwoCycle D (Q.vertex ⟨0,hb⟩) (Q.vertex r))
    (colour : Fin n → Bool) (hne : ∃ i j, colour (Q.vertex i) ≠ colour (Q.vertex j))
    (L : Nat) (hL : 0 < L) (hLb : L < b)
    (hpaths : ∀ P : UPath D, P.support ⊆ Q.support → P.vertices.length = L+1 → colour P.first = colour P.last) :
    (∀ i, colour (Q.vertex i) ≠ colour (Q.vertex (cyclicSucc i))) ∧
      colour (Q.vertex ⟨0,hb⟩) ≠ colour (Q.vertex r) := by
  let f := cycleColour Q hb colour
  have hfb : NatPeriod f b := cycleColour_period Q hb colour
  have hfL : NatPeriod f L := no_crossing_period Q hb colour L hLb hpaths
  have hnf : ∃ i j, f i ≠ f j := by
    obtain ⟨i,j,hij⟩ := hne
    refine ⟨i.val,j.val,?_⟩
    simpa [f,cycleColour,index,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hij
  obtain ⟨m,hm2,hmhalf,hfm,hmb,hmL,hmin⟩ := least_short_period f b L hb hL hLb hfb hfL hnf
  have hmr : m < r.val := chord_beyond_period Q hb r hrlo he colour L m hL hLb (by omega) hfm hmb hmL
    (fun q hq => (hmin q).1 hq) hpaths
  let Q' := Q.rotate r
  let back : Fin b := ⟨b-r.val,by omega⟩
  have hback : 1 < back.val := by dsimp [back]; omega
  have hbackedge : TwoCycle D (Q'.vertex ⟨0,hb⟩) (Q'.vertex back) := by
    rw [Q.rotate_zero,Q.rotate_back r (by omega)]
    exact twoCycle_symm D he
  have hfm' : NatPeriod (cycleColour Q' hb colour) m := (cycleColour_rotate_period Q r hb colour m).2 hfm
  have hpaths' : ∀ P : UPath D, P.support ⊆ Q'.support → P.vertices.length = L+1 → colour P.first = colour P.last := by
    intro P hPQ hlen
    rw [Q.rotate_support] at hPQ
    exact hpaths P hPQ hlen
  have hmback := chord_beyond_period Q' hb back hback hbackedge colour L m hL hLb (by omega) hfm' hmb hmL
    (fun q hq => (hmin q).1 ((cycleColour_rotate_period Q r hb colour q).1 hq)) hpaths'
  have hrb : r.val+m < b := by dsimp [back] at hmback; omega
  obtain ⟨hf2,hzero⟩ := far_chord_period_two Q hb r he colour L m hL hLb (by omega) hfm hmb hmL hmr hrb hpaths
  have halt := period_two_alternates f hf2 hnf
  constructor
  · intro i
    have hi := halt i.val
    simpa [f,cycleColour,index,cyclicSucc,Nat.mod_eq_of_lt i.isLt] using hi
  · have hi := (halt r.val).symm
    change f 0 = f (r.val+1) at hzero
    rw [← hzero] at hi
    simpa [f,cycleColour,index,Nat.mod_eq_of_lt r.isLt] using hi

theorem chord_crossing_path (Q : UCycle D b) (hb : 0 < b) (r : Fin b)
    (hrlo : 1 < r.val) (hrhi : r.val+1 < b)
    (he : TwoCycle D (Q.vertex ⟨0,hb⟩) (Q.vertex r))
    (colour : Fin n → Bool) (hne : ∃ i j, colour (Q.vertex i) ≠ colour (Q.vertex j))
    (hbad : (∃ i, colour (Q.vertex i) = colour (Q.vertex (cyclicSucc i))))
    (L : Nat) (hL : 0 < L) (hLb : L < b) :
    ∃ P : UPath D, P.support ⊆ Q.support ∧ P.vertices.length = L+1 ∧ colour P.first ≠ colour P.last := by
  classical
  by_contra hn
  have hpaths : ∀ P : UPath D, P.support ⊆ Q.support → P.vertices.length = L+1 → colour P.first = colour P.last := by
    intro P hPQ hlen
    by_contra hne
    exact hn ⟨P,hPQ,hlen,hne⟩
  have hh := chord_no_crossing_bipartition Q hb r hrlo hrhi he colour hne L hL hLb hpaths
  obtain ⟨i,hi⟩ := hbad
  exact hh.1 i hi

end ChvatalErdos

#print axioms ChvatalErdos.chord_no_crossing_bipartition
#print axioms ChvatalErdos.chord_crossing_path
