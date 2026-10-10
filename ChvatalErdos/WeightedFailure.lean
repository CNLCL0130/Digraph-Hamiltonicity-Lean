import ChvatalErdos.CaroWei
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace ChvatalErdos
open FiniteProbability

theorem linear_exp_tail_antitone (K t c : ℝ) (hK : 0 ≤ K) (ht : K ≤ t)
    (hc : 0 < c) (hscale : c ≤ K + 1) :
    (t + 1) * Real.exp (-t / c) ≤ (K + 1) * Real.exp (-K / c) := by
  have hratio : 1 ≤ (K + 1) / c := (le_div_iff₀ hc).2 (by linarith)
  have hdiff : 0 ≤ t - K := sub_nonneg.mpr ht
  have h1 : t + 1 ≤ (K + 1) * (1 + (t - K) / c) := by
    have h := mul_le_mul_of_nonneg_right hratio hdiff
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((t - K) / c))
    (show 0 ≤ K + 1 by linarith)
  have h3 : t + 1 ≤ (K + 1) * Real.exp ((t - K) / c) := by linarith
  have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-t / c)).le
  have heq : ((K + 1) * Real.exp ((t - K) / c)) * Real.exp (-t / c) =
      (K + 1) * Real.exp (-K / c) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at h4
  exact h4

theorem degree_weighted_failure_sum {n : Nat} (D : Digraph (Fin n)) (a : Nat)
    (ha : AlphaTwoLE D a) (d : Fin n → ℝ) (K c : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hscale : c ≤ K + 1)
    (hmin : ∀ v, K ≤ d v) (hdegree : ∀ v, (twoCycleDegree D v : ℝ) ≤ d v) :
    (∑ v : Fin n, Real.exp (-d v / c)) ≤
      (a : ℝ) * (K + 1) * Real.exp (-K / c) := by
  have hv : ∀ v, Real.exp (-d v / c) ≤
      ((K + 1) * Real.exp (-K / c)) * (1 / ((twoCycleDegree D v : ℝ) + 1)) := by
    intro v
    have ht := linear_exp_tail_antitone K (d v) c hK (hmin v) hc hscale
    have hdeg := mul_le_mul_of_nonneg_right (hdegree v) (Real.exp_pos (-d v / c)).le
    have hprod : Real.exp (-d v / c) * ((twoCycleDegree D v : ℝ) + 1) ≤
        (K + 1) * Real.exp (-K / c) := by nlinarith
    have hden : 0 < (twoCycleDegree D v : ℝ) + 1 := by positivity
    simpa only [div_eq_mul_inv, one_mul] using (le_div_iff₀ hden).2 hprod
  calc
    _ ≤ ∑ v : Fin n, ((K + 1) * Real.exp (-K / c)) *
        (1 / ((twoCycleDegree D v : ℝ) + 1)) := Finset.sum_le_sum (fun v _ => hv v)
    _ = ((K + 1) * Real.exp (-K / c)) *
        (∑ v : Fin n, 1 / ((twoCycleDegree D v : ℝ) + 1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((K + 1) * Real.exp (-K / c)) * a :=
      mul_le_mul_of_nonneg_left (caro_wei D a ha) (by positivity)
    _ = _ := by ring

theorem degree_weighted_union_bound {n : Nat} {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (D : Digraph (Fin n)) (a : Nat) (ha : AlphaTwoLE D a)
    (A : Fin n → Finset Ω) (d : Fin n → ℝ) (K c : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hscale : c ≤ K + 1)
    (hmin : ∀ v, K ≤ d v) (hdegree : ∀ v, (twoCycleDegree D v : ℝ) ≤ d v)
    (hprob : ∀ v, prob (A v) ≤ Real.exp (-d v / c)) :
    prob (Finset.univ.biUnion A) ≤ (a : ℝ) * (K + 1) * Real.exp (-K / c) := by
  exact (prob_biUnion_le Finset.univ A).trans
    ((Finset.sum_le_sum (fun v _ => hprob v)).trans
      (degree_weighted_failure_sum D a ha d K c hK hc hscale hmin hdegree))

end ChvatalErdos

#print axioms ChvatalErdos.degree_weighted_union_bound
