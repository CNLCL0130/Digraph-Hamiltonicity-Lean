import ChvatalErdos.AsymptoticFinite

set_option autoImplicit false

namespace ChvatalErdos

theorem scale_power_bound (ε : ℝ) (hε : 0 < ε) (a : Nat) (ha : 3 ≤ a) :
    asymptoticScale a ≤ (24/(ε^4*Real.log (Real.log 3)^2))*(a : ℝ)^(1+ε) := by
  have haR : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  let L := Real.log (a : ℝ)
  let t := Real.log L
  let t₀ := Real.log (Real.log 3)
  have hL : 0 < L := Real.log_pos (by linarith)
  have ht₀ : 0 < t₀ := Real.log_pos log_three_gt_one
  have ht₀t : t₀ ≤ t := Real.log_le_log (by linarith [log_three_gt_one]) (Real.log_le_log (by norm_num) haR)
  have ht : 0 < t := ht₀.trans_le ht₀t
  have hpow := Real.pow_div_factorial_le_exp (ε*L) (mul_nonneg hε.le hL.le) 4
  norm_num [Nat.factorial] at hpow
  have hexp : Real.exp (ε*L) = (a : ℝ)^ε := by rw [Real.rpow_def_of_pos hapos]; congr 1; dsimp [L]; ring
  rw [hexp] at hpow
  have hlogpow : L^4 ≤ (24/ε^4)*(a : ℝ)^ε := by
    apply (mul_le_mul_iff_right₀ (pow_pos hε 4)).mp
    have he : ε^4*((24/ε^4)*(a : ℝ)^ε) = 24*(a : ℝ)^ε := by field_simp
    rw [he]
    nlinarith only [hpow]
  have hden : t₀^2 ≤ t^2 := by nlinarith only [ht₀t,ht₀,ht]
  have hscale : asymptoticScale a ≤ (a : ℝ)*L^4/t₀^2 := by
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht₀) hden
  have hnum := mul_le_mul_of_nonneg_left hlogpow hapos.le
  have hdiv := div_le_div_of_nonneg_right hnum (sq_nonneg t₀)
  apply hscale.trans
  convert hdiv using 1
  rw [Real.rpow_add hapos,Real.rpow_one]
  dsimp [t₀]
  field_simp

def EpsilonClaim : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
  ∀ a : Nat, 3 ≤ a → ∃ K : Nat, SufficientBound a K ∧ (K : ℝ) ≤ C*(a : ℝ)^(1+ε)

theorem epsilon_claim : EpsilonClaim := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := asymptotic_claim
  let B := 24/(ε^4*Real.log (Real.log 3)^2)
  have hlog : 0 < Real.log (Real.log 3) := Real.log_pos log_three_gt_one
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C*B,mul_pos hC hB,?_⟩
  intro a ha
  obtain ⟨K,hK,hKa⟩ := hbound a ha
  refine ⟨K,hK,?_⟩
  have hscale := mul_le_mul_of_nonneg_left (scale_power_bound ε hε a ha) hC.le
  have hKa' : (K : ℝ) ≤ C*asymptoticScale a := by
    simpa only [asymptoticScale,mul_div_assoc,mul_assoc] using hKa
  exact hKa'.trans (by simpa only [B,mul_assoc] using hscale)

end ChvatalErdos

#print axioms ChvatalErdos.epsilon_claim
