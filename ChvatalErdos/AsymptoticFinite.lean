import ChvatalErdos.AsymptoticLarge

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

theorem log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  have hh := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) (by decide : 0 < 3)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hh
  have he : Real.exp 1 < 3 := by linarith
  have hl := Real.log_lt_log (Real.exp_pos 1) he
  simpa only [Real.log_exp] using hl

theorem loglog_pos (a : Nat) (ha : 3 ≤ a) : 0 < Real.log (Real.log (a : ℝ)) := by
  have haR : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) haR
  exact Real.log_pos (lt_of_lt_of_le log_three_gt_one hl)

theorem asymptoticScale_nonneg (a : Nat) : 0 ≤ asymptoticScale a := by
  unfold asymptoticScale
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (sq_nonneg _)

theorem asymptoticScale_pos (a : Nat) (ha : 3 ≤ a) : 0 < asymptoticScale a := by
  have haR : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hl : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  have hll := loglog_pos a ha
  dsimp [asymptoticScale]
  positivity

theorem asymptotic_claim : AsymptoticClaim := by
  let N := ⌈Real.exp 4⌉₊
  let K₂ := fun a => remainderBudget a 2+connectionBudget a 2
  let C₀ := ∑ a ∈ Finset.range N, ((K₂ a : ℝ)/asymptoticScale a)
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun a _ => div_nonneg (Nat.cast_nonneg _) (asymptoticScale_nonneg a))
  refine ⟨largeConstant+C₀,by linarith [largeConstant_pos],?_⟩
  intro a ha
  have hscale := asymptoticScale_pos a ha
  by_cases haN : N ≤ a
  · have he : Real.exp 4 ≤ (a : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast haN)
    have hl := Real.log_le_log (Real.exp_pos 4) he
    rw [Real.log_exp] at hl
    obtain ⟨K,hK,hbound⟩ := large_asymptotic_bound a (by omega) hl
    refine ⟨K,hK,?_⟩
    have hh := mul_le_mul_of_nonneg_right (show largeConstant ≤ largeConstant+C₀ by linarith) hscale.le
    have hf : (K : ℝ) ≤ (largeConstant+C₀)*asymptoticScale a := hbound.trans hh
    simpa only [asymptoticScale,mul_div_assoc,mul_assoc] using hf
  · have hamem : a ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hr : (K₂ a : ℝ)/asymptoticScale a ≤ C₀ :=
      Finset.single_le_sum (fun b _ => div_nonneg (Nat.cast_nonneg _) (asymptoticScale_nonneg b)) hamem
    have hbound := (div_le_iff₀ hscale).mp hr
    refine ⟨K₂ a,quantitative_k_two a (by omega),?_⟩
    have hh := mul_nonneg largeConstant_pos.le hscale.le
    have hf : (K₂ a : ℝ) ≤ (largeConstant+C₀)*asymptoticScale a := by nlinarith only [hbound,hh]
    simpa only [asymptoticScale,mul_div_assoc,mul_assoc] using hf

end ChvatalErdos

#print axioms ChvatalErdos.asymptotic_claim
