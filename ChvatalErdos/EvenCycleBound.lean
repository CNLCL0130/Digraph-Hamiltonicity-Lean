import ChvatalErdos.PikhurkoDegree
import ChvatalErdos.QuantitativeK2

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

theorem even_cycle_degree_bound_large (k : Nat) (hk : 3 ≤ k) : EvenCycleDegreeBound k := by
  intro n D hno
  have hmass : edgeMass D Finset.univ = ∑ v : Fin n, (twoCycleDegree D v : ℝ) := by
    simp [edgeMass,degreeMass,twoCycleDegree]
  rw [← hmass]
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k : ℝ)-1 := by linarith
  by_cases hn : n = 0
  · subst n
    simp only [edgeMass,Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,mul_zero,add_zero]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let δ := edgeMass D Finset.univ/(2*n)
  have hrep : 2*δ*n = edgeMass D Finset.univ := by dsimp [δ]; field_simp
  by_cases hδ : 0 < δ
  · obtain ⟨U,hU,hdeg⟩ := exists_degree_core D δ hδ (Nat.pos_of_ne_zero hn) hrep.le
    have hbound := no_even_cycle_min_degree D U hU hk hno δ hdeg
    have hmul := mul_le_mul_of_nonneg_right hbound hnR.le
    have hpow : (n : ℝ)^(1+1/(k : ℝ)) = (n : ℝ)*(n : ℝ)^(1/(k : ℝ)) := by
      rw [Real.rpow_add hnR,Real.rpow_one]
    rw [hpow]
    nlinarith
  · have hδ0 : δ ≤ 0 := le_of_not_gt hδ
    have hmass0 : edgeMass D Finset.univ ≤ 0 := by nlinarith
    apply hmass0.trans
    positivity

theorem even_cycle_degree_bound (k : Nat) (hk : 2 ≤ k) : EvenCycleDegreeBound k := by
  by_cases htwo : k = 2
  · simpa only [htwo] using even_cycle_degree_bound_two
  · exact even_cycle_degree_bound_large k (by omega)

theorem quantitative_claim : QuantitativeClaim := by
  intro a k ha hk hthree
  exact quantitative_of_even_cycle_bound a k ha hk hthree (even_cycle_degree_bound k hk)

end ChvatalErdos

#print axioms ChvatalErdos.even_cycle_degree_bound
#print axioms ChvatalErdos.quantitative_claim
