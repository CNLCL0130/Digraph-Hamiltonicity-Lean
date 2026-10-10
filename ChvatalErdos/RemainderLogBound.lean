import ChvatalErdos.LogBudgets

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChvatalErdos

theorem remainder_log_bound (a k : Nat) (ha : 1 ≤ a) (hk : 2 ≤ k)
    (L t x : ℝ) (hL : 1 ≤ L) (ht : 0 < t) (hx : 1 ≤ x)
    (hloga : Real.log (a : ℝ) = L) (hlogL : Real.log L = t)
    (hxt : x*t = L) (hklow : x ≤ (k : ℝ)-1) (hkhigh : (k : ℝ) ≤ 4*x) :
    (remainderBudget a k : ℝ) ≤ (8*Real.exp 2+131)*(a : ℝ)*x^2*L^2 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  let s := (k : ℝ)-1
  have hs : 1 ≤ s := by dsimp [s]; linarith
  have hspos : 0 < s := by linarith
  have hB : 0 < 2*s*(a : ℝ) := by positivity
  have hlogs : Real.log (2*s) ≤ 2*s := (Real.log_le_sub_one_of_pos (by positivity : 0 < 2*s)).trans (by linarith)
  have hloga_s : L/s ≤ t := by
    apply (div_le_iff₀ hspos).mpr
    have hh := mul_le_mul_of_nonneg_right hklow ht.le
    dsimp [s] at *
    nlinarith [hxt]
  have hlogB : Real.log (2*s*(a : ℝ))/s ≤ t+2 := by
    rw [Real.log_mul (by positivity) (by positivity),hloga,add_div]
    have hh : Real.log (2*s)/s ≤ 2 := (div_le_iff₀ hspos).mpr (by linarith)
    linarith
  have hexp : Real.exp (Real.log (2*s*(a : ℝ))/s) ≤ L*Real.exp 2 := by
    have hh := Real.exp_le_exp.mpr hlogB
    rw [Real.exp_add,← hlogL,Real.exp_log (by linarith : 0 < L)] at hh
    exact hh
  have hkexp : (k : ℝ)/s = 1+1/s := by
    have hsne : (k : ℝ)-1 ≠ 0 := by linarith
    dsimp [s]; field_simp [hsne]; ring
  have hpower : (2*s*(a : ℝ))^((k : ℝ)/s) ≤ 8*Real.exp 2*(a : ℝ)*x*L := by
    rw [hkexp,Real.rpow_add hB,Real.rpow_one,Real.rpow_def_of_pos hB]
    have hh := mul_le_mul_of_nonneg_left hexp hB.le
    have hsx : s ≤ 4*x := by dsimp [s]; linarith
    have hh2 := mul_le_mul_of_nonneg_right hsx (show 0 ≤ 2*(a : ℝ)*L*Real.exp 2 by positivity)
    simp only [one_div] at ⊢
    simp only [div_eq_mul_inv] at hh
    nlinarith only [hh,hh2]
  have hratio : (k : ℝ)/s ≤ 2 := (div_le_iff₀ hspos).mpr (by dsimp [s]; linarith)
  have hlinear : (32*(k : ℝ)+(k : ℝ)/s)*(a : ℝ) ≤ 130*(a : ℝ)*x := by
    have hh : 32*(k : ℝ)+(k : ℝ)/s ≤ 130*x := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ (a : ℝ) by positivity)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2*s*(a : ℝ))^((k : ℝ)/s)+(32*(k : ℝ)+(k : ℝ)/s)*(a : ℝ) by positivity)
  change (remainderBudget a k : ℝ) < (2*s*(a : ℝ))^((k : ℝ)/s)+(32*(k : ℝ)+(k : ℝ)/s)*(a : ℝ)+1 at hceil
  have hxL : 1 ≤ x*L := by nlinarith only [hx,hL,mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ L-1 by linarith)]
  have hxLsq : x*L ≤ x^2*L^2 := by nlinarith only [hxL,sq_nonneg (x*L-1)]
  have hxSq : x ≤ x^2*L^2 := by nlinarith only [hxLsq,mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ L-1 by linarith)]
  have hp := mul_le_mul_of_nonneg_left hxLsq (show 0 ≤ 8*Real.exp 2*(a : ℝ) by positivity)
  have hl := mul_le_mul_of_nonneg_left hxSq (show 0 ≤ 130*(a : ℝ) by positivity)
  have hone : 1 ≤ (a : ℝ)*x^2*L^2 := by nlinarith only [hx,hxSq,mul_nonneg (show 0 ≤ (a : ℝ)-1 by linarith) (show 0 ≤ x^2*L^2 by positivity)]
  nlinarith only [hceil,hpower,hlinear,hp,hl,hone]

end ChvatalErdos

#print axioms ChvatalErdos.remainder_log_bound
