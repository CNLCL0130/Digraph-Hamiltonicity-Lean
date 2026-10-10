import ChvatalErdos.Core
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ChvatalErdos

namespace CycleEndpoints

def index {b : Nat} (hb : 0 < b) (n : Nat) : Fin b := ⟨n % b, Nat.mod_lt n hb⟩

def shiftThree {b : Nat} (i : Fin b) : Fin b :=
  index (Nat.zero_lt_of_lt i.isLt) (i.val + 3)

theorem shiftThree_ne {b : Nat} (hb : 4 ≤ b) (i : Fin b) : i ≠ shiftThree i := by
  intro h
  have heq := congrArg Fin.val h
  change i.val = (i.val + 3) % b at heq
  by_cases hc : i.val + 3 < b
  · rw [Nat.mod_eq_of_lt hc] at heq
    omega
  · have hlow : b ≤ i.val + 3 := by omega
    have hhigh : i.val + 3 - b < b := by omega
    rw [Nat.mod_eq_sub_mod hlow, Nat.mod_eq_of_lt hhigh] at heq
    omega

/-- The unordered endpoint pairs of complementary paths have distance three on the circle. -/
def graph (b : Nat) : Digraph (Fin b) where
  arc i j := i ≠ j ∧ (j = shiftThree i ∨ i = shiftThree j)
  loopless _ h := h.1 rfl

theorem graph_symmetric (b : Nat) (i j : Fin b) (h : (graph b).arc i j) :
    (graph b).arc j i := ⟨Ne.symm h.1, h.2.symm⟩

theorem graph_step {b : Nat} (hb : 4 ≤ b) (i : Fin b) :
    (graph b).arc i (shiftThree i) := ⟨shiftThree_ne hb i, Or.inl rfl⟩

theorem reach_three_mul {b : Nat} (hb : 4 ≤ b) (i : Fin b) (m : Nat) :
    Reach (graph b) (fun _ => True) i
      (index (by omega : 0 < b) (i.val + 3 * m)) := by
  induction m with
  | zero =>
    have heq : index (by omega : 0 < b) (i.val + 3 * 0) = i := by
      apply Fin.ext
      simp [index, Nat.mod_eq_of_lt i.isLt]
    rw [heq]
    exact Reach.refl True.intro
  | succ m ih =>
    have heq : shiftThree (index (by omega : 0 < b) (i.val + 3 * m)) =
        index (by omega : 0 < b) (i.val + 3 * (m + 1)) := by
      apply Fin.ext
      simp [shiftThree, index, Nat.mul_add, Nat.add_assoc]
    rw [← heq]
    exact Reach.step ih (graph_step hb _) True.intro

theorem inverse_three (b : Nat) (h : ¬ 3 ∣ b) : ∃ n q : Nat, 3 * n = q * b + 1 := by
  have hmod : b % 3 ≠ 0 := by
    intro hz
    exact h (Nat.dvd_of_mod_eq_zero hz)
  have hlt := Nat.mod_lt b (by decide : 0 < 3)
  have hdiv := Nat.mod_add_div b 3
  have hcases : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hcases with h₁ | h₂
  · exact ⟨2 * (b / 3) + 1, 2, by omega⟩
  · exact ⟨b / 3 + 1, 1, by omega⟩

theorem reach_one {b : Nat} (hb : 4 ≤ b) (hthree : ¬ 3 ∣ b) (i : Fin b) :
    Reach (graph b) (fun _ => True) i (index (by omega : 0 < b) (i.val + 1)) := by
  obtain ⟨n, q, hn⟩ := inverse_three b hthree
  have h := reach_three_mul hb i n
  have heq : index (by omega : 0 < b) (i.val + 3 * n) =
      index (by omega : 0 < b) (i.val + 1) := by
    apply Fin.ext
    simp [index, hn, Nat.add_mod]
  rwa [heq] at h

theorem reach_add {b : Nat} (hb : 4 ≤ b) (hthree : ¬ 3 ∣ b) (i : Fin b) (m : Nat) :
    Reach (graph b) (fun _ => True) i (index (by omega : 0 < b) (i.val + m)) := by
  induction m with
  | zero =>
    have heq : index (by omega : 0 < b) (i.val + 0) = i := by
      apply Fin.ext
      simp [index, Nat.mod_eq_of_lt i.isLt]
    rw [heq]
    exact Reach.refl True.intro
  | succ m ih =>
    have h := reach_one hb hthree (index (by omega : 0 < b) (i.val + m))
    have heq : index (by omega : 0 < b)
        ((index (by omega : 0 < b) (i.val + m)).val + 1) =
        index (by omega : 0 < b) (i.val + (m + 1)) := by
      apply Fin.ext
      simp [index, Nat.add_assoc]
    rw [heq] at h
    exact reach_trans (graph b) (fun _ => True) ih h

theorem connected {b : Nat} (hb : 4 ≤ b) (hthree : ¬ 3 ∣ b) :
    StrongOn (graph b) (fun _ => True) := by
  refine ⟨⟨⟨0, by omega⟩, True.intro⟩, ?_⟩
  intro i j _ _
  have h := reach_add hb hthree i (b - i.val + j.val)
  have heq : index (by omega : 0 < b) (i.val + (b - i.val + j.val)) = j := by
    apply Fin.ext
    have harith : i.val + (b - i.val + j.val) = b + j.val := by omega
    simp [index, harith, Nat.mod_eq_of_lt j.isLt]
  rwa [heq] at h

/-- The combinatorial effective-outcome existence statement for a circle of length b. -/
theorem mixed_cycle_has_effective_pair {b : Nat} (hb : 4 ≤ b) (hthree : ¬ 3 ∣ b)
    (left right : Fin b → Prop)
    (exclusive : ∀ i, left i → right i → False)
    (mixed_left : ¬ ∀ i, left i) (mixed_right : ¬ ∀ i, right i) :
    ∃ i j, (j = shiftThree i ∨ i = shiftThree j) ∧ ¬ right i ∧ ¬ left j := by
  obtain ⟨i, j, hij, hi, hj⟩ := effective_pair_of_connected (graph b)
    (graph_symmetric b) (fun i => ⟨shiftThree i, graph_step hb i⟩)
    (connected hb hthree) left right exclusive mixed_left mixed_right
  exact ⟨i, j, hij.2, hi, hj⟩

end CycleEndpoints

end ChvatalErdos

#print axioms ChvatalErdos.CycleEndpoints.connected
#print axioms ChvatalErdos.CycleEndpoints.mixed_cycle_has_effective_pair
