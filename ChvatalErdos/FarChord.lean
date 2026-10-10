import ChvatalErdos.OneChordPaths
import ChvatalErdos.CyclePeriods
import ChvatalErdos.ResidueSplit

set_option autoImplicit false

namespace ChvatalErdos
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

theorem far_chord_period_two (Q : UCycle D b) (hb : 0 < b) (r : Fin b)
    (he : TwoCycle D (Q.vertex ⟨0,hb⟩) (Q.vertex r))
    (colour : Fin n → Bool) (L m : Nat) (hL : 0 < L) (hLb : L < b) (hm : 0 < m)
    (hfm : NatPeriod (cycleColour Q hb colour) m) (hmb : m ∣ b) (hmL : m ∣ L)
    (hmr : m < r.val) (hrb : r.val+m < b)
    (hpaths : ∀ P : UPath D, P.support ⊆ Q.support → P.vertices.length = L+1 → colour P.first = colour P.last) :
    NatPeriod (cycleColour Q hb colour) 2 ∧
      cycleColour Q hb colour 0 = cycleColour Q hb colour (r.val+1) := by
  let f := cycleColour Q hb colour
  have hfb : NatPeriod f b := cycleColour_period Q hb colour
  have hfL : NatPeriod f L := no_crossing_period Q hb colour L hLb hpaths
  obtain ⟨hmLle,hgap⟩ := period_multiple_gap b m L hm hL hLb hmb hmL
  have hminus : ∀ u, u < m → f (b-u) = f (r.val+u+1) := by
    intro u hu
    obtain ⟨s,t,hs,ht,hst,hsmod⟩ := split_with_residue b m r.val L u hm hu hmLle hgap hmr hrb
    obtain ⟨P,hPQ,hPlen,hfirst,hlast⟩ := Q.chord_cross_minus r (by omega) he s t hs ht
    have hcol := hpaths P hPQ (by rw [hPlen]; omega)
    rw [hfirst,hlast] at hcol
    change f (b-s) = f (r.val-t) at hcol
    have hsu : Nat.ModEq m s u := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hu] using hsmod
    have hstart : f (b-s) = f (b-u) := hfm.eq_of_modEq f (Nat.ModEq.sub_left (by omega) (by omega) hsu)
    have hend : f (r.val-t) = f (r.val+u+1) := by
      rw [← hfL (r.val-t)]
      have heq : r.val-t+L = r.val+s+1 := by omega
      rw [heq]
      exact hfm.eq_of_modEq f ((hsu.add_left r.val).add_right 1)
    exact hstart.symm.trans (hcol.trans hend)
  have hplus : ∀ u, u < m → f (b-u) = f (r.val+u-1) := by
    intro u hu
    obtain ⟨s,t,hs,ht,hst,hsmod⟩ := split_with_residue b m (b-r.val) L ((b-u)%m) hm (Nat.mod_lt _ hm)
      hmLle hgap (by omega) (by omega)
    have hs' : s < r.val := by have hr := r.isLt; omega
    obtain ⟨P,hPQ,hPlen,hfirst,hlast⟩ := Q.chord_cross_plus r (by omega) he s t hs' ht
    have hcol := hpaths P hPQ (by rw [hPlen]; omega)
    rw [hfirst,hlast] at hcol
    change f s = f (r.val+t) at hcol
    have hsu : Nat.ModEq m s (b-u) := hsmod
    have hstart : f s = f (b-u) := hfm.eq_of_modEq f hsu
    have hbL : Nat.ModEq m b L := by simp only [Nat.ModEq,Nat.mod_eq_zero_of_dvd hmb,Nat.mod_eq_zero_of_dvd hmL]
    have hsadd : Nat.ModEq m (s+u) L := by
      have h := hsu.add_right u
      have heq : b-u+u = b := by omega
      rw [heq] at h
      exact h.trans hbL
    have hboth : Nat.ModEq m (s+(r.val+u-1)) (s+(r.val+t)) := by
      have h := (hsadd.add_left r.val).sub_right (by omega : 1 ≤ r.val+(s+u)) (by omega : 1 ≤ r.val+L)
      have hleft : r.val+(s+u)-1 = s+(r.val+u-1) := by omega
      have hright : r.val+L-1 = s+(r.val+t) := by omega
      simpa only [hleft,hright] using h
    have hend : f (r.val+t) = f (r.val+u-1) := hfm.eq_of_modEq f (hboth.add_left_cancel' s).symm
    exact hstart.symm.trans (hcol.trans hend)
  refine ⟨?_,?_⟩
  · by_contra hn
    obtain ⟨j,hj,hneq⟩ := period_difference_block f m hm hfm 2 (r.val-1) hn
    have he := (hminus j hj).symm.trans (hplus j hj)
    have hleft : r.val-1+j = r.val+j-1 := by omega
    have hright : r.val-1+j+2 = r.val+j+1 := by omega
    exact hneq (by rw [hright,hleft]; exact he.symm)
  · have hzero : f b = f 0 := by simpa using hfb 0
    simpa only [Nat.sub_zero,hzero,Nat.add_zero] using hminus 0 hm

end ChvatalErdos

#print axioms ChvatalErdos.far_chord_period_two
