import ChvatalErdos.OneChordPaths
import ChvatalErdos.CyclePeriods
import ChvatalErdos.ResidueSplit

set_option autoImplicit false

namespace ChvatalErdos
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

theorem chord_beyond_period (Q : UCycle D b) (hb : 0 < b) (r : Fin b) (hr : 1 < r.val)
    (he : TwoCycle D (Q.vertex ⟨0,hb⟩) (Q.vertex r))
    (colour : Fin n → Bool) (L m : Nat) (hL : 0 < L) (hLb : L < b) (hm : 0 < m)
    (hfm : NatPeriod (cycleColour Q hb colour) m) (hmb : m ∣ b) (hmL : m ∣ L)
    (hmin : ∀ q, NatPeriod (cycleColour Q hb colour) q → m ∣ q)
    (hpaths : ∀ P : UPath D, P.support ⊆ Q.support → P.vertices.length = L+1 → colour P.first = colour P.last) :
    m < r.val := by
  let f := cycleColour Q hb colour
  have hfb : NatPeriod f b := cycleColour_period Q hb colour
  have hfL : NatPeriod f L := no_crossing_period Q hb colour L hLb hpaths
  obtain ⟨hmLle,hgap⟩ := period_multiple_gap b m L hm hL hLb hmb hmL
  by_contra h
  have hrm : r.val ≤ m := by omega
  have hnq : ¬NatPeriod f (r.val-1) := by
    intro hp
    have hd := hmin _ hp
    have hh := Nat.le_of_dvd (by omega : 0 < r.val-1) hd
    omega
  obtain ⟨j,hjm,hj⟩ := period_difference_block f m hm hfm (r.val-1) (b-m+1) hnq
  let s := m-1-j
  have hs : s < L := by dsimp [s]; omega
  have hstart : b-m+1+j = b-s := by dsimp [s]; omega
  obtain ⟨P,hPQ,hPlen,hfirst,hlast⟩ := Q.chord_forward_path r (by omega) he s L hs (by omega)
  have hcol := hpaths P hPQ hPlen
  rw [hfirst,hlast] at hcol
  change f (b-s) = f (r.val+L-s-1) at hcol
  have hshift : f (b-s+(r.val-1)) = f (r.val+L-s-1) := by
    rw [← hfL (b-s+(r.val-1))]
    have heq : b-s+(r.val-1)+L = r.val+L-s-1+b := by omega
    rw [heq,hfb]
  rw [hstart] at hj
  exact hj (hcol.trans hshift.symm)

end ChvatalErdos

#print axioms ChvatalErdos.chord_beyond_period
