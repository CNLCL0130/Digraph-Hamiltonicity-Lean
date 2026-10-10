import ChvatalErdos.FourCycle
import ChvatalErdos.ExtremalReduction

set_option autoImplicit false

namespace ChvatalErdos

theorem even_cycle_degree_bound_two : EvenCycleDegreeBound 2 := by
  intro n D hfree
  have h := four_cycle_degree_bound D hfree
  norm_num only [Nat.cast_ofNat,show (2 : ℝ)-1 = 1 by norm_num,mul_one] at *
  exact h

/-- The k = 2 case of the manuscript's quantitative bound, with no external
extremal premise. This is not the general-k or asymptotic theorem. -/
theorem quantitative_k_two (a : Nat) (ha : 2 ≤ a) :
    SufficientBound a (remainderBudget a 2 + connectionBudget a 2) :=
  quantitative_of_even_cycle_bound a 2 ha (by decide) (by decide) even_cycle_degree_bound_two

end ChvatalErdos

#print axioms ChvatalErdos.quantitative_k_two
