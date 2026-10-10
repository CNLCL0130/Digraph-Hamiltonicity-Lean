import ChvatalErdos.FiniteProbability

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.FiniteProbability
variable {Ω V : Type} [Fintype Ω] [DecidableEq Ω]

theorem conditional_union_bound (E H : Finset Ω) (C : Finset V) (events : V → Finset Ω)
    (hcover : ∀ x ∈ E ∩ H, ∃ z ∈ C, x ∈ events z) (c : ℝ)
    (hbound : ∀ z ∈ C, prob (events z ∩ H) / prob H ≤ c) :
    prob (E ∩ H) / prob H ≤ (C.card : ℝ)*c := by
  have hsub : E ∩ H ⊆ C.biUnion (fun z => events z ∩ H) := by
    intro x hx
    obtain ⟨z,hz,hxE⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_inter.mpr ⟨hxE,(Finset.mem_inter.mp hx).2⟩⟩
  calc
    _ ≤ prob (C.biUnion (fun z => events z ∩ H)) / prob H :=
      div_le_div_of_nonneg_right (prob_mono hsub) (prob_nonneg H)
    _ ≤ (∑ z ∈ C, prob (events z ∩ H)) / prob H :=
      div_le_div_of_nonneg_right (prob_biUnion_le C _) (prob_nonneg H)
    _ = ∑ z ∈ C, prob (events z ∩ H) / prob H := by simp only [div_eq_mul_inv,Finset.sum_mul]
    _ ≤ ∑ _z ∈ C, c := Finset.sum_le_sum hbound
    _ = _ := by simp

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.conditional_union_bound
