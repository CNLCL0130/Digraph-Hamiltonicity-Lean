import ChvatalErdos.NatPeriods
import ChvatalErdos.CycleSegments

set_option autoImplicit false

namespace ChvatalErdos
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

def cycleColour (Q : UCycle D b) (hb : 0 < b) (colour : Fin n → Bool) (i : Nat) : Bool :=
  colour (Q.vertex (index hb i))

theorem cycleColour_period (Q : UCycle D b) (hb : 0 < b) (colour : Fin n → Bool) :
    NatPeriod (cycleColour Q hb colour) b := by
  intro i
  simp [cycleColour,index]

theorem no_crossing_period (Q : UCycle D b) (hb : 0 < b) (colour : Fin n → Bool)
    (L : Nat) (hL : L < b)
    (hpaths : ∀ P : UPath D, P.support ⊆ Q.support → P.vertices.length = L+1 → colour P.first = colour P.last) :
    NatPeriod (cycleColour Q hb colour) L := by
  intro i
  let start := index hb i
  have hp := hpaths (Q.segment start L hL) (Q.segment_support start L hL) (Q.segment_length start L hL)
  rw [Q.segment_first,Q.segment_last] at hp
  have he : index hb (start.val+L) = index hb (i+L) := by
    apply Fin.ext
    simp [start,index,Nat.add_mod]
  rw [he] at hp
  exact hp.symm

theorem period_difference_block (f : Nat → Bool) (m : Nat) (hm : 0 < m)
    (hfm : NatPeriod f m) (q start : Nat) (hnq : ¬NatPeriod f q) :
    ∃ j : Nat, j < m ∧ f (start+j) ≠ f (start+j+q) := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp hnq
  obtain ⟨j,hj⟩ := (offsetEquiv hm (start%m) (Nat.mod_lt start hm)).surjective (index hm i)
  have hj' : (start+j.val)%m = i%m := by
    have hh := congrArg Fin.val hj
    dsimp [offsetEquiv,index] at hh
    simpa only [Nat.add_mod,Nat.mod_mod,Nat.add_comm] using hh
  refine ⟨j.val,j.isLt,?_⟩
  intro he
  have hi0 : f (start+j.val) = f i := by rw [hfm.reduce f (start+j.val),hfm.reduce f i,hj']
  have hiq : f (start+j.val+q) = f (i+q) := by
    rw [hfm.reduce f (start+j.val+q),hfm.reduce f (i+q)]
    congr 1
    simpa only [Nat.add_mod,Nat.mod_mod] using congrArg (fun v => (v+q%m)%m) hj'
  exact hi ((hiq.symm.trans he.symm).trans hi0)

end ChvatalErdos

#print axioms ChvatalErdos.no_crossing_period
#print axioms ChvatalErdos.period_difference_block
