import ChvatalErdos.CyclePeriods

set_option autoImplicit false

namespace ChvatalErdos
open CycleEndpoints
variable {n b : Nat} {D : Digraph (Fin n)}

def UCycle.rotate (Q : UCycle D b) (r : Fin b) : UCycle D b :=
  ⟨Q.rotated r,Q.rotated_injective r,Q.rotated_edge r⟩

theorem UCycle.rotate_support (Q : UCycle D b) (r : Fin b) : (Q.rotate r).support = Q.support := by
  ext v
  rw [UCycle.mem_support,Q.rotated_range r]
  rfl

theorem UCycle.rotate_zero (Q : UCycle D b) (r : Fin b) (hb : 0 < b) :
    (Q.rotate r).vertex ⟨0,hb⟩ = Q.vertex r := by
  simp [rotate,rotated,index,Nat.mod_eq_of_lt r.isLt]

theorem UCycle.rotate_back (Q : UCycle D b) (r : Fin b) (hr : 0 < r.val) :
    (Q.rotate r).vertex ⟨b-r.val,by omega⟩ = Q.vertex ⟨0,by omega⟩ := by
  have he : b-r.val+r.val = b := by have h := r.isLt; omega
  simp [rotate,rotated,index,he]

theorem cycleColour_rotate (Q : UCycle D b) (r : Fin b) (hb : 0 < b) (colour : Fin n → Bool) (i : Nat) :
    cycleColour (Q.rotate r) hb colour i = cycleColour Q hb colour (i+r.val) := by
  simp [cycleColour,UCycle.rotate,UCycle.rotated,index,Nat.mod_add_mod]

theorem NatPeriod.shift {A : Type} (f : Nat → A) {p : Nat} (hp : NatPeriod f p) (s : Nat) :
    NatPeriod (fun i => f (i+s)) p := by
  intro i
  simpa only [Nat.add_right_comm i p s] using hp (i+s)

theorem NatPeriod.shift_iff {A : Type} (f : Nat → A) {b p s : Nat} (hfb : NatPeriod f b) (hs : s ≤ b) :
    NatPeriod (fun i => f (i+s)) p ↔ NatPeriod f p := by
  refine ⟨?_,fun hp => hp.shift f s⟩
  intro hp i
  have h := hp (i+b-s)
  have he1 : i+b-s+s = i+b := by omega
  have he2 : i+b-s+p+s = i+p+b := by omega
  change f (i+b-s+p+s) = f (i+b-s+s) at h
  rw [he1,he2,hfb,hfb] at h
  exact h

theorem cycleColour_rotate_period (Q : UCycle D b) (r : Fin b) (hb : 0 < b) (colour : Fin n → Bool) (p : Nat) :
    NatPeriod (cycleColour (Q.rotate r) hb colour) p ↔ NatPeriod (cycleColour Q hb colour) p := by
  have heq : cycleColour (Q.rotate r) hb colour = fun i => cycleColour Q hb colour (i+r.val) :=
    funext (cycleColour_rotate Q r hb colour)
  rw [heq]
  exact NatPeriod.shift_iff _ (cycleColour_period Q hb colour) (by have h := r.isLt; omega)

end ChvatalErdos

#print axioms ChvatalErdos.cycleColour_rotate_period
