import ChvatalErdos.Chernoff

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.FiniteProbability
variable {I A S : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] [Nonempty A]

/-- Average a coordinate separately by exchanging it with an independent copy. -/
theorem expectation_coordinate_update (f : (I → A) → ℝ) (i : I) :
    expectation f = expectation (fun a : A => expectation (fun x : I → A => f (Function.update x i a))) := by
  let swap : A × (I → A) → A × (I → A) := fun p => (p.2 i,Function.update p.2 i p.1)
  have hswap : Function.Involutive swap := by
    intro p
    apply Prod.ext
    · simp [swap]
    · funext k
      by_cases hk : k = i
      · subst k; simp [swap]
      · simp [swap,Function.update_of_ne hk]
  let e : A × (I → A) ≃ A × (I → A) := ⟨swap,swap,hswap,hswap⟩
  have he := expectation_equiv e (fun p : A × (I → A) => f p.2)
  rw [expectation_prod,expectation_prod] at he
  simpa only [e,swap,Equiv.coe_fn_mk,expectation_const] using he.symm

def freeze (seen : Finset I) (fixed x : I → A) : I → A :=
  fun i => if i ∈ seen then fixed i else x i

theorem freeze_update (seen : Finset I) (fixed x : I → A) (i : I) (hi : i ∉ seen) (a : A) :
    freeze seen fixed (Function.update x i a) = freeze (insert i seen) (Function.update fixed i a) x := by
  funext k
  by_cases hk : k = i
  · subst k; simp [freeze,hi]
  · by_cases hs : k ∈ seen <;> simp [freeze,hk,hs,Function.update_of_ne hk]

/-- A stopped branch has weight zero before the requested number of queries.
This permits an overflow bound directly, without introducing padding samples. -/
noncomputable def survivalWeight (query : S → Option I) (advance : S → I → A → S)
    (success : S → I → A → Bool) : Nat → S → (I → A) → ℝ
  | 0, _, _ => 1
  | n+1, s, x => match query s with
    | none => 0
    | some i => Real.exp (-Real.log 2 * (if success s i (x i) then (1 : ℝ) else 0)) *
        survivalWeight query advance success n (advance s i (x i)) x

theorem survivalWeight_nonneg (query : S → Option I) (advance : S → I → A → S)
    (success : S → I → A → Bool) (n : Nat) (s : S) (x : I → A) :
    0 ≤ survivalWeight query advance success n s x := by
  induction n generalizing s with
  | zero => simp [survivalWeight]
  | succ n ih =>
    cases hq : query s with
    | none => simp [survivalWeight,hq]
    | some i =>
      simp only [survivalWeight,hq]
      exact mul_nonneg (Real.exp_pos _).le (ih _)

theorem fresh_survival_laplace (query : S → Option I) (advance : S → I → A → S)
    (seen : S → Finset I) (success : S → I → A → Bool)
    (hqfresh : ∀ s i, query s = some i → i ∉ seen s)
    (hadvance : ∀ s i a, seen (advance s i a) = insert i (seen s))
    (p : ℝ) (hp : p ≤ 1)
    (hlower : ∀ s i, query s = some i →
      p ≤ prob (Finset.univ.filter (fun a : A => success s i a = true)))
    (n : Nat) (s : S) (fixed : I → A) :
    expectation (fun x => survivalWeight query advance success n s (freeze (seen s) fixed x)) ≤
      (1-p/2)^n := by
  induction n generalizing s fixed with
  | zero => simp [survivalWeight,expectation_const]
  | succ n ih =>
    cases hq : query s with
    | none =>
      simp only [survivalWeight,hq,expectation_const]
      apply pow_nonneg
      linarith
    | some i =>
      have hi := hqfresh s i hq
      have hsplit : expectation (fun x => survivalWeight query advance success (n+1) s
          (freeze (seen s) fixed x)) =
          expectation (fun a : A => Real.exp (-Real.log 2 * (if success s i a then (1 : ℝ) else 0)) *
            expectation (fun x : I → A => survivalWeight query advance success n (advance s i a)
              (freeze (seen (advance s i a)) (Function.update fixed i a) x))) := by
        rw [expectation_coordinate_update _ i]
        congr 1
        funext a
        rw [← expectation_const_mul]
        congr 1
        funext x
        rw [freeze_update _ _ _ i hi a]
        have hv : freeze (insert i (seen s)) (Function.update fixed i a) x i = a := by simp [freeze]
        simp only [survivalWeight,hq,hv,hadvance]
      rw [hsplit]
      calc
        _ ≤ expectation (fun a : A =>
            Real.exp (-Real.log 2 * (if success s i a then (1 : ℝ) else 0)) * (1-p/2)^n) := by
          apply expectation_mono
          intro a
          exact mul_le_mul_of_nonneg_left (ih (advance s i a) (Function.update fixed i a)) (Real.exp_pos _).le
        _ = (1 - prob (Finset.univ.filter (fun a : A => success s i a = true))/2) * (1-p/2)^n := by
          rw [expectation_mul_const]
          congr 1
          convert bernoulli_laplace (Finset.univ.filter (fun a : A => success s i a = true)) using 1
          simp
        _ ≤ (1-p/2)^(n+1) := by
          rw [pow_succ']
          apply mul_le_mul_of_nonneg_right
          · linarith [hlower s i hq]
          · apply pow_nonneg; linarith

/-- The exponential estimate for any event on which the surviving weight is
at least the usual Chernoff threshold. -/
theorem survival_weight_tail {Ω : Type} [Fintype Ω] (weight : Ω → ℝ)
    (hnonneg : ∀ x, 0 ≤ weight x) (μ : ℝ) (hμ : 0 ≤ μ)
    (hmean : expectation weight ≤ Real.exp (-μ/2)) (E : Finset Ω)
    (hE : ∀ x ∈ E, Real.exp (-Real.log 2 * (μ/2)) ≤ weight x) :
    prob E ≤ Real.exp (-μ/8) := by
  have hm := markov weight hnonneg (Real.exp (-Real.log 2 * (μ/2))) (Real.exp_pos _)
  have hsub : E ⊆ Finset.univ.filter (fun x => Real.exp (-Real.log 2 * (μ/2)) ≤ weight x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE x hx⟩
  have hr := div_le_div_of_nonneg_right hmean (Real.exp_pos (-Real.log 2 * (μ/2))).le
  have he : Real.exp (-μ/2) / Real.exp (-Real.log 2 * (μ/2)) ≤ Real.exp (-μ/8) := by
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right log_two_lt_three_quarters.le hμ
    nlinarith
  exact (prob_mono hsub).trans (hm.trans (hr.trans he))

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.fresh_survival_laplace
#print axioms ChvatalErdos.FiniteProbability.survival_weight_tail
