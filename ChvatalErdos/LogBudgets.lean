import ChvatalErdos.Targets
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace ChvatalErdos

theorem log_two_lower : (1 : ℝ)/2 ≤ Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh ⊢
  exact hh

theorem colourCount_log_bound (a : Nat) (ha : 2 ≤ a) :
    (colourCount a : ℝ) ≤ 2*Real.log (a : ℝ)+2 := by
  have hcpos := Nat.clog_pos (by decide : 1 < 2) ha
  have hpow := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < a)
  have hpowR : (2 : ℝ)^(Nat.clog 2 a-1) < a := by exact_mod_cast hpow
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2^(Nat.clog 2 a-1)) hpowR
  rw [Real.log_pow] at hlog
  have hcR : ((Nat.clog 2 a-1 : Nat) : ℝ) = (Nat.clog 2 a : ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hcR] at hlog
  have hmul := mul_le_mul_of_nonneg_left log_two_lower (by exact_mod_cast Nat.zero_le (Nat.clog 2 a-1) : 0 ≤ ((Nat.clog 2 a-1 : Nat) : ℝ))
  rw [hcR] at hmul
  dsimp [colourCount]
  push_cast
  linarith

theorem choose_length_parameter (x : ℝ) (hx : 1 ≤ x) :
    ∃ k : Nat, 2 ≤ k ∧ ¬3 ∣ k ∧ x ≤ (k : ℝ)-1 ∧ (k : ℝ) ≤ x+3 := by
  let t := ⌈x⌉₊+1
  have hceil := Nat.le_ceil x
  have hceilUpper := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  have ht : 2 ≤ t := by
    have hh : (1 : ℝ) ≤ ⌈x⌉₊ := hx.trans hceil
    have hhN : 1 ≤ ⌈x⌉₊ := by exact_mod_cast hh
    dsimp [t]; omega
  have htlow : x ≤ (t : ℝ)-1 := by dsimp [t]; push_cast; linarith
  have hthigh : (t : ℝ) < x+2 := by dsimp [t]; push_cast; linarith
  by_cases ht3 : 3 ∣ t
  · refine ⟨t+1,by omega,?_,?_,?_⟩
    · intro hh
      have hd : 3 ∣ 1 := by have hd := Nat.dvd_sub' hh ht3; simpa using hd
      norm_num at hd
    · push_cast; linarith
    · push_cast; linarith
  · exact ⟨t,ht,ht3,htlow,by linarith⟩

end ChvatalErdos

#print axioms ChvatalErdos.colourCount_log_bound
#print axioms ChvatalErdos.choose_length_parameter
