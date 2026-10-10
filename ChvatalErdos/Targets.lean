import ChvatalErdos.Core
import ChvatalErdos.Remainder
import Mathlib.Data.Nat.Log

/-!
Explicit target statements from the manuscript. Defining a proposition is not
proving it. Neither `QuantitativeClaim` nor `AsymptoticClaim` is proved here.
-/

set_option autoImplicit false

namespace ChvatalErdos

def colourCount (a : Nat) : Nat := Nat.clog 2 a + 1

noncomputable def remainderBudget (a k : Nat) : Nat :=
  ⌈(2 * ((k : ℝ) - 1) * (a : ℝ)) ^ ((k : ℝ) / ((k : ℝ) - 1)) +
    (32 * (k : ℝ) + (k : ℝ) / ((k : ℝ) - 1)) * (a : ℝ)⌉₊

def connectionBudget (a k : Nat) : Nat :=
  2 ^ 16 * (2 * k) ^ 2 * a * colourCount a ^ 2

def QuantitativeClaim : Prop :=
  ∀ a k : Nat, 2 ≤ a → 2 ≤ k → ¬ 3 ∣ k →
    SufficientBound a (remainderBudget a k + connectionBudget a k)

/-- Expresses the upper bound by the existence of a sufficient integer K.
This avoids making an unproved existence assumption in a definition of f₂.
-/
def AsymptoticClaim : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a : Nat, 3 ≤ a → ∃ K : Nat,
    SufficientBound a K ∧
    (K : ℝ) ≤ C * (a : ℝ) * Real.log (a : ℝ) ^ 4 /
      Real.log (Real.log (a : ℝ)) ^ 2

end ChvatalErdos
