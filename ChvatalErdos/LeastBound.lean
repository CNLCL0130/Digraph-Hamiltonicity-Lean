import ChvatalErdos.EpsilonBound

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

theorem sufficient_exists (a : Nat) : ∃ K : Nat, SufficientBound a K := by
  obtain ⟨hpos,hall⟩ := quantitative_k_two (a+2) (by omega)
  refine ⟨remainderBudget (a+2) 2+connectionBudget (a+2) 2,hpos,?_⟩
  intro n D hα hstrong
  apply hall n D ?_ hstrong
  intro xs hn hi
  exact (hα xs hn hi).trans (by omega)

/-- The least positive connectivity bound in the manuscript, including its existence. -/
noncomputable def f₂ (a : Nat) : Nat := Nat.find (sufficient_exists a)

theorem f₂_sufficient (a : Nat) : SufficientBound a (f₂ a) := Nat.find_spec (sufficient_exists a)

theorem f₂_pos (a : Nat) : 0 < f₂ a := (f₂_sufficient a).1

theorem f₂_le (a K : Nat) (hK : SufficientBound a K) : f₂ a ≤ K := Nat.find_min' (sufficient_exists a) hK

theorem f₂_quantitative (a k : Nat) (ha : 2 ≤ a) (hk : 2 ≤ k) (hthree : ¬3 ∣ k) :
    f₂ a ≤ remainderBudget a k+connectionBudget a k :=
  f₂_le a _ (quantitative_claim a k ha hk hthree)

theorem f₂_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a : Nat, 3 ≤ a →
    (f₂ a : ℝ) ≤ C*(a : ℝ)*Real.log (a : ℝ)^4/Real.log (Real.log (a : ℝ))^2 := by
  obtain ⟨C,hC,hall⟩ := asymptotic_claim
  refine ⟨C,hC,?_⟩
  intro a ha
  obtain ⟨K,hK,hbound⟩ := hall a ha
  have hh : (f₂ a : ℝ) ≤ K := by exact_mod_cast f₂_le a K hK
  exact hh.trans hbound

theorem f₂_epsilon : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a : Nat, 3 ≤ a → (f₂ a : ℝ) ≤ C*(a : ℝ)^(1+ε) := by
  intro ε hε
  obtain ⟨C,hC,hall⟩ := epsilon_claim ε hε
  refine ⟨C,hC,?_⟩
  intro a ha
  obtain ⟨K,hK,hbound⟩ := hall a ha
  have hh : (f₂ a : ℝ) ≤ K := by exact_mod_cast f₂_le a K hK
  exact hh.trans hbound

end ChvatalErdos

#print axioms ChvatalErdos.f₂_sufficient
#print axioms ChvatalErdos.f₂_quantitative
#print axioms ChvatalErdos.f₂_asymptotic
#print axioms ChvatalErdos.f₂_epsilon
