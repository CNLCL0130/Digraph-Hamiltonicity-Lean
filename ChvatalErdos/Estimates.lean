import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace ChvatalErdos

def selectionK (a b l : ℝ) : ℝ := 65536 * b ^ 2 * a * l ^ 2

theorem selection_exponent (a b l : ℝ) (hb : b ≠ 0) (hl : l ≠ 0) :
    selectionK a b l / (16 * b * l) = 4096 * b * a * l := by
  dsimp [selectionK]
  field_simp
  ring

theorem matching_mean (a b l : ℝ) (hb : b ≠ 0) (hl : l ≠ 0) :
    selectionK a b l / (8 * b ^ 2 * l ^ 2) = 8192 * a := by
  dsimp [selectionK]
  field_simp
  ring

theorem record_exponent (a b l : ℝ) (hb : b ≠ 0) (hl : l ≠ 0) :
    selectionK a b l / (512 * b ^ 2 * l ^ 2) = 128 * a := by
  dsimp [selectionK]
  field_simp
  ring

theorem quadratic_le_exp_large (x : ℝ) (hx : 384 ≤ x) :
    64 * x ^ 2 ≤ Real.exp x := by
  have hx₀ : 0 ≤ x := by linarith
  have h := Real.pow_div_factorial_le_exp x hx₀ 3
  norm_num [Nat.factorial] at h
  have hm := mul_nonneg (sq_nonneg x) (show 0 ≤ x - 384 by linarith)
  nlinarith

theorem absorb_prefactor (a b l : ℝ) (ha : 2 ≤ a) (hb : 4 ≤ b) (hl : 1 ≤ l) :
    2 * selectionK a b l * Real.exp (-(selectionK a b l / (16 * b * l))) ≤
      Real.exp (-(selectionK a b l / (32 * b * l))) := by
  have ha₀ : 0 < a := by linarith
  have hb₀ : 0 < b := by linarith
  have hl₀ : 0 < l := by linarith
  let x := 2048 * b * a * l
  have hba : 8 ≤ b * a := by
    have h := mul_le_mul hb ha (by norm_num : (0 : ℝ) ≤ 2) hb₀.le
    norm_num at h
    exact h
  have hbal : 8 ≤ b * a * l := by
    have h := mul_le_mul hba hl (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ b * a)
    norm_num at h
    exact h
  have hx : 384 ≤ x := by dsimp [x]; nlinarith
  have hx₀ : 0 < x := by linarith
  have hbl : b * l ≤ x := by
    calc
      b * l = 1 * (b * l) := by ring
      _ ≤ (2048 * a) * (b * l) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = x := by dsimp [x]; ring
  have hKx : 2 * selectionK a b l = 64 * (b * l) * x := by
    dsimp [selectionK, x]
    ring
  have hpref : 2 * selectionK a b l ≤ Real.exp x := by
    apply le_trans _ (quadratic_le_exp_large x hx)
    have h := mul_le_mul_of_nonneg_right hbl (show 0 ≤ 64 * x by positivity)
    rw [hKx]
    nlinarith
  have hexp₁ : selectionK a b l / (16 * b * l) = 2 * x := by
    rw [selection_exponent a b l hb₀.ne' hl₀.ne']
    dsimp [x]
    ring
  have hexp₂ : selectionK a b l / (32 * b * l) = x := by
    dsimp [selectionK, x]
    field_simp
    ring
  rw [hexp₁, hexp₂]
  have h := mul_le_mul_of_nonneg_right hpref (Real.exp_pos (-(2 * x))).le
  have heq : Real.exp x * Real.exp (-(2 * x)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq] at h

theorem one_record_tail (a b l : ℝ) (ha : 2 ≤ a) (hb : 4 ≤ b) (hl : 1 ≤ l) :
    Real.exp (-(selectionK a b l / (256 * b ^ 2 * l))) +
      2 * selectionK a b l * Real.exp (-(selectionK a b l / (16 * b * l))) +
      Real.exp (-(selectionK a b l / (64 * b ^ 2 * l ^ 2))) ≤
      3 * Real.exp (-(selectionK a b l / (512 * b ^ 2 * l ^ 2))) := by
  have ha₀ : 0 < a := by linarith
  have hb₀ : 0 < b := by linarith
  have hl₀ : 0 < l := by linarith
  have e₁ : selectionK a b l / (256 * b ^ 2 * l) = 256 * a * l := by
    dsimp [selectionK]
    field_simp
    ring
  have e₂ : selectionK a b l / (32 * b * l) = 2048 * b * a * l := by
    dsimp [selectionK]
    field_simp
    ring
  have e₃ : selectionK a b l / (64 * b ^ 2 * l ^ 2) = 1024 * a := by
    dsimp [selectionK]
    field_simp
    ring
  have hal : a ≤ a * l := by nlinarith
  have hbal : 4 ≤ b * l := by nlinarith [mul_nonneg (show 0 ≤ b - 4 by linarith) (show 0 ≤ l - 1 by linarith)]
  have hlarge : 128 * a ≤ 2048 * b * a * l := by
    have h := mul_le_mul_of_nonneg_right hbal ha₀.le
    nlinarith
  have h₁ : Real.exp (-(selectionK a b l / (256 * b ^ 2 * l))) ≤ Real.exp (-128 * a) := by
    rw [e₁]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h₂ := absorb_prefactor a b l ha hb hl
  have h₂' : Real.exp (-(selectionK a b l / (32 * b * l))) ≤ Real.exp (-128 * a) := by
    rw [e₂]
    apply Real.exp_le_exp.mpr
    linarith
  have h₃ : Real.exp (-(selectionK a b l / (64 * b ^ 2 * l ^ 2))) ≤ Real.exp (-128 * a) := by
    rw [e₃]
    apply Real.exp_le_exp.mpr
    linarith
  rw [record_exponent a b l hb₀.ne' hl₀.ne']
  have hneg : -(128 * a) = -128 * a := by ring
  rw [hneg]
  linarith

/-- A polynomial lower bound for exp suffices at the actual parameter range. -/
theorem cubic_exp_tail (x : ℝ) (hx : 32768 ≤ x) :
    64 * x ^ 3 * Real.exp (-x) < (1 : ℝ) / 16 := by
  have hx₀ : 0 < x := by linarith
  have hexp := Real.pow_div_factorial_le_exp x hx₀.le 4
  norm_num at hexp
  have hpoly : 1024 * x ^ 3 < x ^ 4 / 24 := by
    have hm := mul_pos (pow_pos hx₀ 3) (show 0 < x - 24576 by linarith)
    nlinarith
  have hlt : 1024 * x ^ 3 < Real.exp x := lt_of_lt_of_le hpoly hexp
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos x)).2
  linarith

theorem six_mul_le_exp_two_mul (a : ℝ) (ha : 2 ≤ a) :
    6 * a ≤ Real.exp (2 * a) := by
  have h := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * a by linarith) 3
  norm_num [Finset.sum_range_succ] at h
  have hprod : 0 ≤ a * (a - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The neighbour-failure estimate, with all parameters substituted. -/
theorem neighbour_failure (a b l : ℝ) (ha : 2 ≤ a) (hb : 4 ≤ b) (hl : 1 ≤ l) :
    2 * a * l * (selectionK a b l + 3) *
      Real.exp (-(selectionK a b l / (16 * b * l))) < (1 : ℝ) / 16 := by
  have ha₀ : 0 < a := by linarith
  have hb₀ : 0 < b := by linarith
  have hl₀ : 0 < l := by linarith
  let x := 4096 * b * a * l
  have hba : 8 ≤ b * a := by
    have h := mul_le_mul hb ha (by norm_num : (0 : ℝ) ≤ 2) hb₀.le
    norm_num at h
    exact h
  have hbal : 8 ≤ b * a * l := by
    have h := mul_le_mul hba hl (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ b * a)
    norm_num at h
    exact h
  have hx : 32768 ≤ x := by dsimp [x]; nlinarith
  have hx₀ : 0 < x := by linarith
  have hal : a * l ≤ x := by
    calc
      a * l = 1 * (a * l) := by ring
      _ ≤ (4096 * b) * (a * l) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = x := by dsimp [x]; ring
  have hbl : b * l ≤ x := by
    calc
      b * l = 1 * (b * l) := by ring
      _ ≤ (4096 * a) * (b * l) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = x := by dsimp [x]; ring
  have hKx : selectionK a b l = 16 * (b * l) * x := by
    dsimp [selectionK, x]
    ring
  have hKup : selectionK a b l + 3 ≤ 32 * x ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hbl (show 0 ≤ 16 * x by positivity)
    rw [hKx]
    nlinarith
  have hcoef : 2 * a * l * (selectionK a b l + 3) ≤ 64 * x ^ 3 := by
    have h := mul_le_mul (show 2 * a * l ≤ 2 * x by linarith) hKup
      (by dsimp [selectionK]; positivity : 0 ≤ selectionK a b l + 3)
      (by positivity : 0 ≤ 2 * x)
    nlinarith
  rw [selection_exponent a b l hb₀.ne' hl₀.ne']
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-x)).le) (cubic_exp_tail x hx)

theorem all_records_tail (a : Nat) (l : ℝ) (ha : 2 ≤ a)
    (hlmax : l ≤ 2 * (a : ℝ)) :
    3 * l * (9 : ℝ) ^ a * Real.exp (-128 * (a : ℝ)) < (1 : ℝ) / 16 := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have h9 : (9 : ℝ) ≤ Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hp : (9 : ℝ) ^ a ≤ (Real.exp 3) ^ a := pow_le_pow_left₀ (by norm_num) h9 a
  have hpow : (Real.exp 3) ^ a = Real.exp (3 * (a : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow] at hp
  have hlb : 3 * l ≤ Real.exp (2 * (a : ℝ)) :=
    le_trans (by linarith) (six_mul_le_exp_two_mul a haR)
  have hprod : 3 * l * (9 : ℝ) ^ a ≤
      Real.exp (2 * (a : ℝ)) * Real.exp (3 * (a : ℝ)) :=
    mul_le_mul hlb hp (by positivity) (Real.exp_pos _).le
  have hbound := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-128 * (a : ℝ))).le
  have hsimp : Real.exp (2 * (a : ℝ)) * Real.exp (3 * (a : ℝ)) *
      Real.exp (-128 * (a : ℝ)) = Real.exp (-123 * (a : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hsimp] at hbound
  have hexp : (16 : ℝ) < Real.exp (123 * (a : ℝ)) := by
    have h := Real.add_one_le_exp (123 * (a : ℝ))
    linarith
  have hsmall : Real.exp (-123 * (a : ℝ)) < (1 : ℝ) / 16 := by
    rw [neg_mul, Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) hexp
  exact lt_of_le_of_lt hbound hsmall

end ChvatalErdos

#print axioms ChvatalErdos.cubic_exp_tail
#print axioms ChvatalErdos.all_records_tail
#print axioms ChvatalErdos.neighbour_failure
#print axioms ChvatalErdos.one_record_tail
