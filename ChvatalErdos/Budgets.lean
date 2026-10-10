import ChvatalErdos.Core
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace ChvatalErdos

theorem record_count (a : Nat) (ha : 1 ≤ a) :
    Fintype.card (Fin (2 * a - 1) → Fin 3) < 9 ^ a := by
  simp only [Fintype.card_fun,Fintype.card_fin]
  have hpow : 3 ^ (2*a-1) < 3 ^ (2*a) := Nat.pow_lt_pow_right (by omega : 1 < 3) (by omega)
  simpa [Nat.pow_mul] using hpow

def halfUp (c : Nat) : Nat := (c + 1) / 2

theorem halfUp_iterate (c t : Nat) (hc : 1 ≤ c) :
    halfUp^[t] c = (c - 1) / (2 ^ t) + 1 := by
  induction t with
  | zero => simp; omega
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    unfold halfUp
    have h : ((c - 1) / 2 ^ t + 1 + 1) / 2 = ((c - 1) / 2 ^ t) / 2 + 1 := by omega
    rw [h,Nat.div_div_eq_div_mul,Nat.pow_succ]

theorem halving_rounds (a : Nat) (ha : 1 ≤ a) : halfUp^[Nat.clog 2 a] a = 1 := by
  rw [halfUp_iterate a _ ha]
  have h := Nat.le_pow_clog (by omega : 1 < 2) a
  have hlt : a - 1 < 2 ^ Nat.clog 2 a := by omega
  rw [Nat.div_eq_of_lt hlt]

theorem colour_count_bound (a : Nat) (ha : 1 ≤ a) : Nat.clog 2 a + 1 ≤ 2 * a := by
  have hpow : a ≤ 2 ^ a := by
    have h : a < 2 ^ a := Nat.lt_two_pow_self
    omega
  have hlog := (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).2 hpow
  omega

end ChvatalErdos

#print axioms ChvatalErdos.record_count
#print axioms ChvatalErdos.halving_rounds
