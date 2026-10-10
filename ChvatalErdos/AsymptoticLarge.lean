import ChvatalErdos.RemainderLogBound
import ChvatalErdos.EvenCycleBound

set_option autoImplicit false

namespace ChvatalErdos

noncomputable def asymptoticScale (a : Nat) : ℝ :=
  (a : ℝ)*Real.log (a : ℝ)^4/Real.log (Real.log (a : ℝ))^2

noncomputable def largeConstant : ℝ := 8*Real.exp 2+67108995

theorem largeConstant_pos : 0 < largeConstant := by dsimp [largeConstant]; positivity

theorem large_asymptotic_bound (a : Nat) (ha : 2 ≤ a) (hlarge : 4 ≤ Real.log (a : ℝ)) :
    ∃ K : Nat, SufficientBound a K ∧ (K : ℝ) ≤ largeConstant*asymptoticScale a := by
  let L := Real.log (a : ℝ)
  let t := Real.log L
  let x := L/t
  have hL : 4 ≤ L := hlarge
  have hLpos : 0 < L := by linarith
  have ht1 : 1 ≤ t := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hL
    have hlog4 : Real.log 4 = 2*Real.log 2 := by
      have hh := Real.log_pow (2 : ℝ) 2
      norm_num at hh
      exact hh
    rw [hlog4] at hh
    dsimp [t]
    linarith [log_two_lower]
  have ht : 0 < t := by linarith
  have htL : t ≤ L := Real.log_le_self hLpos.le
  have hx : 1 ≤ x := (le_div_iff₀ ht).mpr (by linarith)
  have hxt : x*t = L := by dsimp [x]; field_simp
  obtain ⟨k,hk,hthree,hklow,hkhigh⟩ := choose_length_parameter x hx
  have hkbound : (k : ℝ) ≤ 4*x := by linarith
  have hr := remainder_log_bound a k (by omega) hk L t x (by linarith) ht hx rfl rfl hxt hklow hkbound
  have hcolour : (colourCount a : ℝ) ≤ 4*L := by
    have hh := colourCount_log_bound a ha
    change (colourCount a : ℝ) ≤ 2*L+2 at hh
    linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hc0 : (0 : ℝ) ≤ colourCount a := by positivity
  have hksq : (k : ℝ)^2 ≤ 16*x^2 := by nlinarith
  have hcsq : (colourCount a : ℝ)^2 ≤ 16*L^2 := by nlinarith
  have hprod := mul_le_mul hksq hcsq (sq_nonneg _) (by positivity : 0 ≤ 16*x^2)
  have hconn : (connectionBudget a k : ℝ) ≤ 67108864*(a : ℝ)*x^2*L^2 := by
    simp only [connectionBudget,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 262144*(a : ℝ) by positivity)
    nlinarith
  have hscale : asymptoticScale a = (a : ℝ)*x^2*L^2 := by
    change (a : ℝ)*L^4/t^2 = (a : ℝ)*(L/t)^2*L^2
    field_simp
  refine ⟨remainderBudget a k+connectionBudget a k,quantitative_claim a k ha hk hthree,?_⟩
  rw [Nat.cast_add,hscale]
  dsimp [largeConstant]
  nlinarith

end ChvatalErdos

#print axioms ChvatalErdos.large_asymptotic_bound
