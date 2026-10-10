import ChvatalErdos.LinearLowerBound
import ChvatalErdos.PancyclicObstruction
import ChvatalErdos.AffineBaseProperties
import ChvatalErdos.AffineForest

/-!
Entry point for the manuscript's main conclusions.
The proofs below have no external extremal, probabilistic, or Hamiltonicity premises.
The full proof chain is imported above and checked by outputs/verify.ps1.
-/

set_option autoImplicit false

namespace ChvatalErdos

/-- Theorem 2: the explicit quantitative connectivity bound. -/
theorem main_quantitative (a k : Nat) (ha : 2 ≤ a) (hk : 2 ≤ k) (hthree : ¬3 ∣ k) :
    f₂ a ≤ remainderBudget a k+connectionBudget a k := f₂_quantitative a k ha hk hthree

/-- Theorem 1: the asymptotic bound, uniformly for every integer a at least three. -/
theorem main_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a : Nat, 3 ≤ a →
    (f₂ a : ℝ) ≤ C*(a : ℝ)*Real.log (a : ℝ)^4/Real.log (Real.log (a : ℝ))^2 := f₂_asymptotic

/-- Corollary 3: the bound with every positive fixed exponent increment. -/
theorem main_epsilon : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a : Nat, 3 ≤ a → (f₂ a : ℝ) ≤ C*(a : ℝ)^(1+ε) := f₂_epsilon

/-- The introductory complete bipartite obstruction. -/
theorem main_linear_lower (a : Nat) (ha : 2 ≤ a) : a ≤ f₂ a := f₂_linear_lower a ha

/-- The affine-plane construction in the article's final section. -/
theorem main_pancyclic_construction (q : Nat) (hprime : q.Prime) (hq : 11 ≤ q) :
    ∃ D : Digraph (Fin (4 * (q*q*(q+1)))),
      Hamiltonian D ∧ connectivity D = q*q*(q+1) ∧
      alpha₂ D ≤ 8*q*q+4*q-4 ∧ TriangleFree D ∧
      ¬ Pancyclic D ∧ alpha₂ D+1 ≤ connectivity D :=
  pancyclic_construction q hprime hq

/-- No positive linear connectivity constant guarantees pancyclicity. -/
theorem main_pancyclic_obstruction :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (n : Nat) (D : Digraph (Fin n)),
      Hamiltonian D → c*(alpha₂ D : ℝ) ≤ (connectivity D : ℝ) → Pancyclic D :=
  pancyclic_obstruction

example : QuantitativeClaim := quantitative_claim
example : AsymptoticClaim := asymptotic_claim
example : EpsilonClaim := epsilon_claim

end ChvatalErdos

#print axioms ChvatalErdos.main_quantitative
#print axioms ChvatalErdos.main_asymptotic
#print axioms ChvatalErdos.main_epsilon
#print axioms ChvatalErdos.main_linear_lower
#print axioms ChvatalErdos.main_pancyclic_construction
#print axioms ChvatalErdos.main_pancyclic_obstruction
