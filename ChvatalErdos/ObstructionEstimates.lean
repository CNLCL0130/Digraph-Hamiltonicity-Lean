import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ChvatalErdos

theorem obstruction_prime_exists (c : ℝ) :
    ∃ q : Nat, q.Prime ∧ 11 ≤ q ∧ 8*c < (q : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (8*c)
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max 11 N)
  refine ⟨q, hp, (le_max_left 11 N).trans hq, ?_⟩
  exact hN.trans_le (by exact_mod_cast (le_max_right 11 N).trans hq)

theorem obstruction_ratio_bound (c : ℝ) (hc : 0 < c) (q : Nat)
    (hq : 2 ≤ q) (hlarge : 8*c < (q : ℝ)) :
    c * ((8*q^2+4*q-4 : Nat) : ℝ) < ((q^2*(q+1) : Nat) : ℝ) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hsub : 4 ≤ 8*q^2+4*q := by nlinarith
  have ha : ((8*q^2+4*q-4 : Nat) : ℝ) = 8*(q : ℝ)^2+4*q-4 := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  rw [ha]
  have hbound : 8*(q : ℝ)^2+4*q-4 ≤ 8*(q : ℝ)*((q : ℝ)+1) := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hbound hc.le
  have hsecond := mul_lt_mul_of_pos_right hlarge
    (mul_pos hqpos (by linarith : (0 : ℝ) < (q : ℝ)+1))
  have hsecond' : c*(8*(q : ℝ)*((q : ℝ)+1)) < (q : ℝ)^2*((q : ℝ)+1) := by
    convert hsecond using 1 <;> ring
  push_cast
  exact hfirst.trans_lt hsecond'

theorem obstruction_conjecture_bound (q : Nat) (hq : 11 ≤ q) :
    8*q^2+4*q-4+1 ≤ q^2*(q+1) := by
  have hmul : 12*q^2 ≤ q^2*(q+1) := by
    have hx := Nat.mul_le_mul_left (q^2) (by omega : 12 ≤ q+1)
    simpa [Nat.mul_comm] using hx
  have hq2 : q ≤ q^2 := by nlinarith
  have hsimple : 8*q^2+4*q+1 ≤ 12*q^2 := by nlinarith
  have hsub : 8*q^2+4*q-4+1 ≤ 8*q^2+4*q+1 := by omega
  exact hsub.trans (hsimple.trans hmul)

end ChvatalErdos

#print axioms ChvatalErdos.obstruction_prime_exists
#print axioms ChvatalErdos.obstruction_ratio_bound
#print axioms ChvatalErdos.obstruction_conjecture_bound
