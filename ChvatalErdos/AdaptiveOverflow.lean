import ChvatalErdos.Chernoff

set_option autoImplicit false

namespace ChvatalErdos.FiniteProbability

variable {σ α : Type} [Fintype α] [Nonempty α] [DecidableEq α]

def adaptiveCount (success : σ → α → Bool) (advance : σ → α → σ) :
    (n : Nat) → σ → (Fin n → α) → Nat
  | 0, _, _ => 0
  | n + 1, s, x => (if success s (x 0) then 1 else 0) +
      adaptiveCount success advance n (advance s (x 0)) (Fin.tail x)

theorem adaptive_laplace_power (success : σ → α → Bool) (advance : σ → α → σ)
    (p : ℝ) (hp₁ : p ≤ 1)
    (hlower : ∀ s, p ≤ prob (Finset.univ.filter (fun a => success s a = true)))
    (n : Nat) (s : σ) :
    expectation (fun x : Fin n → α =>
      Real.exp (-Real.log 2 * (adaptiveCount success advance n s x : ℝ))) ≤
      (1 - p / 2) ^ n := by
  induction n generalizing s with
  | zero => simp [adaptiveCount, expectation_const]
  | succ n ih =>
    rw [expectation_fin_cons]
    have hfactor : (fun a : α => expectation (fun x : Fin n → α =>
        Real.exp (-Real.log 2 * (adaptiveCount success advance (n + 1) s
          (Fin.cons a x) : ℝ)))) =
        (fun a => Real.exp (-Real.log 2 * (if success s a then (1 : ℝ) else 0)) *
          expectation (fun x : Fin n → α => Real.exp (-Real.log 2 *
            (adaptiveCount success advance n (advance s a) x : ℝ)))) := by
      funext a
      simp only [adaptiveCount, Fin.cons_zero, Fin.tail_cons, Nat.cast_add]
      simp only [mul_add, Real.exp_add, expectation_const_mul]
      cases success s a <;> simp
    rw [hfactor]
    calc
      _ ≤ expectation (fun a =>
          Real.exp (-Real.log 2 * (if success s a then (1 : ℝ) else 0)) *
            (1 - p / 2) ^ n) := by
        apply expectation_mono
        intro a
        exact mul_le_mul_of_nonneg_left (ih (advance s a)) (Real.exp_pos _).le
      _ = (1 - prob (Finset.univ.filter (fun a => success s a = true)) / 2) *
          (1 - p / 2) ^ n := by
        rw [expectation_mul_const]
        congr 1
        convert bernoulli_laplace (Finset.univ.filter (fun a => success s a = true)) using 1
        simp
      _ ≤ (1 - p / 2) ^ (n + 1) := by
        rw [pow_succ']
        apply mul_le_mul_of_nonneg_right
        · linarith [hlower s]
        · apply pow_nonneg
          linarith

theorem adaptive_chernoff (success : σ → α → Bool) (advance : σ → α → σ)
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hlower : ∀ s, p ≤ prob (Finset.univ.filter (fun a => success s a = true)))
    (n : Nat) (s : σ) :
    prob (Finset.univ.filter (fun x : Fin n → α =>
      (adaptiveCount success advance n s x : ℝ) ≤ p * n / 2)) ≤
      Real.exp (-(p * n) / 8) := by
  apply lower_tail_of_laplace _ (p * n) (mul_nonneg hp (Nat.cast_nonneg _))
  apply le_trans (adaptive_laplace_power success advance p hp₁ hlower n s)
  calc
    (1 - p / 2) ^ n ≤ (Real.exp (-p / 2)) ^ n := by
      apply pow_le_pow_left₀ (by linarith)
      linarith [Real.add_one_le_exp (-p / 2)]
    _ = Real.exp (-(p * n) / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.adaptive_laplace_power
#print axioms ChvatalErdos.FiniteProbability.adaptive_chernoff
