import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import ChvatalErdos.CaroWei

set_option autoImplicit false

namespace ChvatalErdos

/-- The analytic step of the remainder bound, separated from its graph-theoretic inputs. -/
theorem sublinear_bound (n C B x₀ p : ℝ)
    (hn : 0 ≤ n) (hx₀ : 0 < x₀)
    (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (fixed_point : C * x₀ ^ p = x₀)
    (initial_bound : n ≤ C * n ^ p + B) :
    n ≤ x₀ + B / (1 - p) := by
  have hden : 0 < 1 - p := by linarith
  have hratio : 0 ≤ n / x₀ := div_nonneg hn hx₀.le
  have hbern := rpow_one_add_le_one_add_mul_self
    (s := n / x₀ - 1) (by linarith : -1 ≤ n / x₀ - 1) hp₀ hp₁.le
  have heq : 1 + (n / x₀ - 1) = n / x₀ := by ring
  rw [heq] at hbern
  have hnrep : n = x₀ * (n / x₀) := by field_simp
  have hpow : C * n ^ p = x₀ * (n / x₀) ^ p := by
    conv_lhs => rw [hnrep]
    rw [Real.mul_rpow hx₀.le hratio, ← mul_assoc, fixed_point]
  have htangent := mul_le_mul_of_nonneg_left hbern hx₀.le
  have hline : x₀ * (1 + p * (n / x₀ - 1)) = x₀ + p * (n - x₀) := by
    field_simp
  rw [hline, ← hpow] at htangent
  have hprod : (n - x₀) * (1 - p) ≤ B := by nlinarith
  have hdiv : n - x₀ ≤ B / (1 - p) := (le_div_iff₀ hden).2 hprod
  linarith

/-- Equation (2.1), deduced from the two scalar extremal inputs. -/
theorem remainder_start (n m a k : ℝ) (hn : 0 < n) (ha : 0 ≤ a)
    (caro_wei : n ^ 2 ≤ a * (2 * m + n))
    (even_cycle_bound : 2 * m ≤ 2 * (k - 1) * n ^ (1 + 1 / k) + 32 * (k - 1) * n) :
    n ≤ 2 * (k - 1) * a * n ^ (1 / k) + (32 * (k - 1) + 1) * a := by
  have hexp : n ^ (1 + 1 / k) = n * n ^ (1 / k) := by
    rw [Real.rpow_add hn, Real.rpow_one]
  rw [hexp] at even_cycle_bound
  have hm := mul_le_mul_of_nonneg_left even_cycle_bound ha
  have hprod : n * n ≤ n * (2 * (k - 1) * a * n ^ (1 / k) +
      (32 * (k - 1) + 1) * a) := by nlinarith
  exact (mul_le_mul_iff_right₀ hn).1 hprod

theorem remainder_scalar_bound (n a k : ℝ) (hn : 0 ≤ n) (ha : 2 ≤ a) (hk : 2 ≤ k)
    (initial_bound : n ≤ 2 * (k - 1) * a * n ^ (1 / k) + (32 * (k - 1) + 1) * a) :
    n ≤ (2 * (k - 1) * a) ^ (k / (k - 1)) + (32 * k + k / (k - 1)) * a := by
  have ha₀ : 0 < a := by linarith
  have hk₀ : 0 < k := by linarith
  have hkm : 0 < k - 1 := by linarith
  let C := 2 * (k - 1) * a
  let x₀ := C ^ (k / (k - 1))
  have hC : 0 < C := by dsimp [C]; positivity
  have hx₀ : 0 < x₀ := Real.rpow_pos_of_pos hC _
  have hp₀ : 0 ≤ 1 / k := by positivity
  have hp₁ : 1 / k < 1 := (div_lt_one hk₀).2 (by linarith)
  have hfixed : C * x₀ ^ (1 / k) = x₀ := by
    dsimp [x₀]
    rw [← Real.rpow_mul hC.le]
    conv_lhs => lhs; rw [← Real.rpow_one C]
    rw [← Real.rpow_add hC]
    congr 1
    field_simp
    ring
  have h := sublinear_bound n C ((32 * (k - 1) + 1) * a) x₀ (1 / k)
    hn hx₀ hp₀ hp₁ hfixed initial_bound
  have hterm : ((32 * (k - 1) + 1) * a) / (1 - 1 / k) =
      (32 * k + k / (k - 1)) * a := by
    field_simp
  rw [hterm] at h
  exact h

theorem remainder_from_degree_bound {N a k : Nat} (D : Digraph (Fin N))
    (hα : AlphaTwoLE D a) (ha : 2 ≤ a) (hk : 2 ≤ k)
    (extremal : (∑ v : Fin N, (twoCycleDegree D v : ℝ)) ≤
      2 * ((k : ℝ) - 1) * (N : ℝ) ^ (1 + 1 / (k : ℝ)) +
        32 * ((k : ℝ) - 1) * (N : ℝ)) :
    (N : ℝ) ≤ (2 * ((k : ℝ) - 1) * (a : ℝ)) ^ ((k : ℝ) / ((k : ℝ) - 1)) +
      (32 * (k : ℝ) + (k : ℝ) / ((k : ℝ) - 1)) * (a : ℝ) := by
  apply remainder_scalar_bound _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast ha) (by exact_mod_cast hk)
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero]
    have hkm : 0 ≤ (k : ℝ) - 1 := by
      have hh : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    positivity
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hcw := caro_wei_density D a hα
    have hin := remainder_start (N : ℝ) ((∑ v : Fin N, (twoCycleDegree D v : ℝ)) / 2)
      (a : ℝ) (k : ℝ) hNpos (Nat.cast_nonneg _)
      (by nlinarith) (by nlinarith)
    exact hin

end ChvatalErdos

#print axioms ChvatalErdos.remainder_scalar_bound
#print axioms ChvatalErdos.remainder_from_degree_bound
