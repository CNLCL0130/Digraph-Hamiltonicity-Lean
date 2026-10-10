import ChvatalErdos.CycleChoice
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false

namespace ChvatalErdos
open CycleEndpoints

theorem residue_in_interval (m start u : Nat) (hm : 0 < m) (hu : u < m) :
    ∃ A, start ≤ A ∧ A < start+m ∧ A%m = u := by
  obtain ⟨j,hj⟩ := (offsetEquiv hm (start%m) (Nat.mod_lt start hm)).surjective ⟨u,hu⟩
  refine ⟨start+j.val,by omega,by have hj := j.isLt; omega,?_⟩
  have hh := congrArg Fin.val hj
  dsimp [offsetEquiv,index] at hh
  simpa only [Nat.add_mod,Nat.mod_mod,Nat.add_comm] using hh

theorem split_with_residue (b m r L u : Nat) (hm : 0 < m) (hu : u < m)
    (hmL : m ≤ L) (hLb : L+m ≤ b) (hmr : m < r) (hrb : r+m < b) :
    ∃ s t, s < b-r ∧ t < r ∧ s+t+1 = L ∧ s%m = u := by
  obtain ⟨s,hslo,hshi,hsmod⟩ := residue_in_interval m (L-r) u hm hu
  have hsL : s < L := by omega
  refine ⟨s,L-s-1,by omega,by omega,by omega,hsmod⟩

theorem period_multiple_gap (b m L : Nat) (hm : 0 < m) (hL : 0 < L) (hLb : L < b)
    (hmb : m ∣ b) (hmL : m ∣ L) : m ≤ L ∧ L+m ≤ b := by
  refine ⟨Nat.le_of_dvd hL hmL,?_⟩
  have hd : m ∣ b-L := Nat.dvd_sub' hmb hmL
  have hg := Nat.le_of_dvd (Nat.sub_pos_of_lt hLb) hd
  omega

end ChvatalErdos

#print axioms ChvatalErdos.split_with_residue
