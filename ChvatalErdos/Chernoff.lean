import ChvatalErdos.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ChvatalErdos.FiniteProbability

theorem log_two_lt_three_quarters : Real.log 2 < (3 : ℝ) / 4 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

section Tail

variable {Ω : Type} [Fintype Ω]

/-- The universal Chernoff step, isolated from the proof of a Laplace-transform bound. -/
theorem lower_tail_of_laplace (Y : Ω → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hLaplace : expectation (fun ω => Real.exp (-Real.log 2 * Y ω)) ≤ Real.exp (-μ / 2)) :
    prob (Finset.univ.filter (fun ω => Y ω ≤ μ / 2)) ≤ Real.exp (-μ / 8) := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsubset : Finset.univ.filter (fun ω => Y ω ≤ μ / 2) ⊆
      Finset.univ.filter (fun ω => Real.exp (-Real.log 2 * (μ / 2)) ≤
        Real.exp (-Real.log 2 * Y ω)) := by
    intro ω hω
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Real.exp_le_exp.mpr ?_⟩
    have h := (Finset.mem_filter.mp hω).2
    nlinarith
  have hm := markov (fun ω => Real.exp (-Real.log 2 * Y ω))
    (fun ω => (Real.exp_pos _).le) (Real.exp (-Real.log 2 * (μ / 2))) (Real.exp_pos _)
  have hr := div_le_div_of_nonneg_right hLaplace (Real.exp_pos (-Real.log 2 * (μ / 2))).le
  have hexp : Real.exp (-μ / 2) / Real.exp (-Real.log 2 * (μ / 2)) ≤ Real.exp (-μ / 8) := by
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right log_two_lt_three_quarters.le hμ
    nlinarith
  exact le_trans (prob_mono hsubset) (le_trans hm (le_trans hr hexp))

end Tail

section Bernoulli

variable {ι α : Type} [Fintype ι] [Fintype α]
  [DecidableEq ι] [DecidableEq α] [Nonempty α]

noncomputable def successCount (A : ι → Finset α) (x : ι → α) : ℝ :=
  ∑ i, if x i ∈ A i then (1 : ℝ) else 0

noncomputable def totalMean (A : ι → Finset α) : ℝ := ∑ i, prob (A i)

omit [Fintype ι] [DecidableEq ι] in
theorem bernoulli_laplace (A : Finset α) :
    expectation (fun x => Real.exp (-Real.log 2 * (if x ∈ A then (1 : ℝ) else 0))) =
      1 - prob A / 2 := by
  have heq : (fun x => Real.exp (-Real.log 2 * (if x ∈ A then (1 : ℝ) else 0))) =
      (fun x => 1 - (if x ∈ A then (1 : ℝ) else 0) / 2) := by
    funext x
    by_cases hx : x ∈ A
    · simp [hx, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    · simp [hx]
  rw [heq, expectation_sub, expectation_const, expectation_div, indicator_expectation]

theorem independent_laplace (A : ι → Finset α) :
    expectation (fun x : ι → α => Real.exp (-Real.log 2 * successCount A x)) ≤
      Real.exp (-totalMean A / 2) := by
  have heq : (fun x : ι → α => Real.exp (-Real.log 2 * successCount A x)) =
      (fun x : ι → α => ∏ i, Real.exp (-Real.log 2 * (if x i ∈ A i then (1 : ℝ) else 0))) := by
    funext x
    simp only [successCount, Finset.mul_sum, Real.exp_sum]
  rw [heq, expectation_product (fun i y => Real.exp (-Real.log 2 * (if y ∈ A i then (1 : ℝ) else 0)))]
  simp_rw [bernoulli_laplace]
  have hp : (∏ i : ι, (1 - prob (A i) / 2)) ≤ ∏ i : ι, Real.exp (-prob (A i) / 2) := by
    apply Finset.prod_le_prod
    · intro i _
      have h := prob_le_one (A i)
      linarith
    · intro i _
      have h := Real.add_one_le_exp (-prob (A i) / 2)
      linarith
  have hexp : (∏ i : ι, Real.exp (-prob (A i) / 2)) = Real.exp (-totalMean A / 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [totalMean, div_eq_mul_inv, Finset.sum_neg_distrib, ← Finset.sum_mul, neg_mul]
  exact le_trans hp hexp.le

/-- Independent Bernoulli lower-tail bound with the paper's constant 1/8. -/
theorem independent_chernoff (A : ι → Finset α) :
    prob (Finset.univ.filter (fun x : ι → α => successCount A x ≤ totalMean A / 2)) ≤
      Real.exp (-totalMean A / 8) := by
  apply lower_tail_of_laplace (successCount A) (totalMean A)
  · exact Finset.sum_nonneg (fun i _ => prob_nonneg (A i))
  · exact independent_laplace A

end Bernoulli

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.lower_tail_of_laplace
#print axioms ChvatalErdos.FiniteProbability.independent_chernoff
