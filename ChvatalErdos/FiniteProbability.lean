import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ChvatalErdos.FiniteProbability

variable {Ω : Type} [Fintype Ω]

/-- Probability in the uniform experiment on a finite sample space. -/
noncomputable def prob (A : Finset Ω) : ℝ := (A.card : ℝ) / (Fintype.card Ω : ℝ)

noncomputable def expectation (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

theorem prob_nonneg (A : Finset Ω) : 0 ≤ prob A := by
  unfold prob
  positivity

theorem prob_mono {A B : Finset Ω} (h : A ⊆ B) : prob A ≤ prob B := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card h

theorem prob_univ [Nonempty Ω] : prob (Finset.univ : Finset Ω) = 1 := by
  simp [prob, Fintype.card_ne_zero]

theorem prob_le_one [Nonempty Ω] (A : Finset Ω) : prob A ≤ 1 := by
  calc
    prob A ≤ prob Finset.univ := prob_mono (Finset.subset_univ A)
    _ = 1 := prob_univ

theorem prob_pos_iff [Nonempty Ω] (A : Finset Ω) : 0 < prob A ↔ A.Nonempty := by
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [prob, div_pos_iff_of_pos_right hΩ, Nat.cast_pos, Finset.card_pos]

theorem prob_union_le [DecidableEq Ω] (A B : Finset Ω) : prob (A ∪ B) ≤ prob A + prob B := by
  unfold prob
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le A B

theorem prob_biUnion_le [DecidableEq Ω] {ι : Type} (s : Finset ι) (A : ι → Finset Ω) :
    prob (s.biUnion A) ≤ ∑ i ∈ s, prob (A i) := by
  unfold prob
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact_mod_cast Finset.card_biUnion_le

theorem expectation_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    expectation f ≤ expectation g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem expectation_const [Nonempty Ω] (c : ℝ) : expectation (fun _ : Ω => c) = c := by
  simp [expectation, Fintype.card_ne_zero]

theorem expectation_sub (f g : Ω → ℝ) :
    expectation (fun ω => f ω - g ω) = expectation f - expectation g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

theorem expectation_div (f : Ω → ℝ) (c : ℝ) :
    expectation (fun ω => f ω / c) = expectation f / c := by
  simp only [expectation, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_right_comm _ _ _

theorem expectation_mul_const (f : Ω → ℝ) (c : ℝ) :
    expectation (fun ω => f ω * c) = expectation f * c := by
  simp only [expectation, ← Finset.sum_mul]
  exact mul_div_right_comm _ _ _

theorem expectation_const_mul (c : ℝ) (f : Ω → ℝ) :
    expectation (fun ω => c * f ω) = c * expectation f := by
  simp only [expectation, ← Finset.mul_sum, mul_div_assoc]

theorem expectation_equiv {Λ : Type} [Fintype Λ] (e : Ω ≃ Λ) (f : Λ → ℝ) :
    expectation (fun ω => f (e ω)) = expectation f := by
  unfold expectation
  rw [e.sum_comp, Fintype.card_congr e]

theorem expectation_prod {Λ : Type} [Fintype Λ] (f : Ω × Λ → ℝ) :
    expectation f = expectation (fun ω => expectation (fun l => f (ω, l))) := by
  unfold expectation
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem expectation_fin_cons {α : Type} [Fintype α] (n : Nat)
    (f : (Fin (n + 1) → α) → ℝ) :
    expectation f = expectation (fun a => expectation (fun x : Fin n → α => f (Fin.cons a x))) := by
  rw [← expectation_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => α)) f, expectation_prod]
  rfl

theorem indicator_expectation [DecidableEq Ω] (A : Finset Ω) :
    expectation (fun ω => if ω ∈ A then (1 : ℝ) else 0) = prob A := by
  simp [expectation, prob, Finset.sum_ite_mem]

/-- Markov's inequality in the exact finite model used for the choices in the paper. -/
theorem markov (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (t : ℝ) (ht : 0 < t) :
    prob (Finset.univ.filter (fun ω => t ≤ f ω)) ≤ expectation f / t := by
  classical
  let A := Finset.univ.filter (fun ω => t ≤ f ω)
  have hs : t * (A.card : ℝ) ≤ ∑ ω, f ω := by
    calc
      t * (A.card : ℝ) = ∑ _ω ∈ A, t := by simp [mul_comm]
      _ ≤ ∑ ω ∈ A, f ω := Finset.sum_le_sum (fun ω hω => (Finset.mem_filter.mp hω).2)
      _ ≤ ∑ ω, f ω := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ A) (fun ω _ _ => hf ω)
  apply (le_div_iff₀ ht).2
  change prob A * t ≤ expectation f
  unfold prob expectation
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa [mul_comm] using hs

/-- Conditional probability for uniform samples reduces to the ratio of event sizes. -/
theorem conditional_eq_card_ratio [DecidableEq Ω] [Nonempty Ω] (A H : Finset Ω) (hH : H.Nonempty) :
    prob (A ∩ H) / prob H = ((A ∩ H).card : ℝ) / (H.card : ℝ) := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hH₀ : (H.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hH).ne'
  unfold prob
  field_simp

theorem prob_eq_sum_fibers {H : Type} [DecidableEq H]
    (g : Ω → H) (s : Finset H) (A : Finset Ω)
    (hmaps : ∀ ω ∈ A, g ω ∈ s) :
    prob A = ∑ h ∈ s, prob (A.filter (fun ω => g ω = h)) := by
  unfold prob
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Uniform conditional bounds are averaged over a partition, not multiplied by
the number of possible histories. -/
theorem average_conditional_bounds [DecidableEq Ω] [Nonempty Ω]
    {H : Type} [DecidableEq H] (g : Ω → H) (A : Finset Ω) (c : ℝ)
    (hbound : ∀ h ∈ Finset.univ.image g,
      prob (A ∩ Finset.univ.filter (fun ω => g ω = h)) /
        prob (Finset.univ.filter (fun ω => g ω = h)) ≤ c) : prob A ≤ c := by
  let s := Finset.univ.image g
  have hnonempty : ∀ h ∈ s, (Finset.univ.filter (fun ω => g ω = h)).Nonempty := by
    intro h hh
    obtain ⟨ω, _, hω⟩ := Finset.mem_image.mp hh
    exact ⟨ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩⟩
  have hfilter : ∀ h, A.filter (fun ω => g ω = h) =
      A ∩ Finset.univ.filter (fun ω => g ω = h) := by
    intro h
    ext ω
    simp
  have hsum : (∑ h ∈ s, prob (Finset.univ.filter (fun ω => g ω = h))) = 1 := by
    rw [← prob_eq_sum_fibers g s Finset.univ (fun ω hω => Finset.mem_image_of_mem g hω)]
    exact prob_univ
  calc
    prob A = ∑ h ∈ s, prob (A.filter (fun ω => g ω = h)) :=
      prob_eq_sum_fibers g s A (fun ω _ => Finset.mem_image_of_mem g (Finset.mem_univ ω))
    _ ≤ ∑ h ∈ s, c * prob (Finset.univ.filter (fun ω => g ω = h)) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [hfilter]
      exact (div_le_iff₀ ((prob_pos_iff _).2 (hnonempty h hh))).mp (hbound h hh)
    _ = c * ∑ h ∈ s, prob (Finset.univ.filter (fun ω => g ω = h)) :=
      (Finset.mul_sum _ _ _).symm
    _ = c := by rw [hsum, mul_one]

section Product

variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq ι]

/-- Factorization of the expectation of a product of coordinate functions. -/
theorem expectation_product (f : ι → α → ℝ) :
    expectation (fun x : ι → α => ∏ i, f i (x i)) =
      ∏ i, expectation (f i) := by
  unfold expectation
  rw [Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum, ← Finset.prod_div_distrib]

end Product

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.markov
#print axioms ChvatalErdos.FiniteProbability.expectation_product
#print axioms ChvatalErdos.FiniteProbability.average_conditional_bounds
