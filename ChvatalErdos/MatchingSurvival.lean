import ChvatalErdos.NegativeAssociation

set_option autoImplicit false

namespace ChvatalErdos.FiniteProbability

theorem expectation_coordinate {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α]
    [DecidableEq ι] (i : ι) (f : α → ℝ) :
    expectation (fun x : ι → α => f (x i)) = expectation f := by
  have h := expectation_product (fun j a => if j = i then f a else 1)
  have hr : (fun j => expectation (fun a => if j = i then f a else 1)) =
      (fun j => if j = i then expectation f else 1) := by
    funext j
    by_cases hj : j = i <;> simp [hj, expectation_const]
  rw [hr] at h
  simpa using h

theorem negAssociated_matching_products {Ω Λ U V I : Type}
    [Fintype Ω] [Fintype Λ] [DecidableEq U] [DecidableEq V] [DecidableEq I]
    (X : Ω → U → ℝ) (Z : Λ → V → ℝ)
    (hX : NegAssociated X) (hZ : NegAssociated Z)
    (hXp : ∀ ω u, 0 ≤ X ω u) (hZp : ∀ z v, 0 ≤ Z z v)
    (u : I → U) (v : I → V) (hu : Function.Injective u) (hv : Function.Injective v) :
    NegAssociated (fun ω : Ω × Λ => fun i => X ω.1 (u i) * Z ω.2 (v i)) := by
  let support : I → Finset (U ⊕ V) := fun i => {Sum.inl (u i), Sum.inr (v i)}
  have hdis : ∀ i j, i ≠ j → Disjoint (support i) (support j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hki hkj
    rcases hki with hki | hki <;> rcases hkj with hkj | hkj
    · exact hij (hu (Sum.inl.inj (hki.symm.trans hkj)))
    · exact Sum.noConfusion (hki.symm.trans hkj)
    · exact Sum.noConfusion (hki.symm.trans hkj)
    · exact hij (hv (Sum.inr.inj (hki.symm.trans hkj)))
  let φ : I → (U ⊕ V → ℝ) → ℝ := fun i x =>
    max 0 (x (Sum.inl (u i))) * max 0 (x (Sum.inr (v i)))
  have hmono : ∀ i, Monotone (φ i) := by
    intro i x y hxy
    exact mul_le_mul (max_le_max le_rfl (hxy _)) (max_le_max le_rfl (hxy _))
      (le_max_left _ _) (le_max_left _ _)
  have hdep : ∀ i, DependsOn (φ i) (support i) := by
    intro i x y hxy
    dsimp [φ]
    rw [hxy (Sum.inl (u i)) (by simp [support]), hxy (Sum.inr (v i)) (by simp [support])]
  have h := negAssociated_disjoint_maps _ (negAssociated_independent_sum X Z hX hZ)
    support hdis φ hmono hdep
  simpa only [φ, Sum.elim_inl, Sum.elim_inr, max_eq_right (hXp _ _),
    max_eq_right (hZp _ _)] using h

structure PartSelection (n : Nat) (α κ : Type) where
  value : Fin n → α → κ → ℝ
  zero_one : ∀ i a j, value i a j = 0 ∨ value i a j = 1
  at_most_one : ∀ i a j k, value i a j ≠ 0 → value i a k ≠ 0 → j = k

namespace PartSelection

variable {n m : Nat} {α β κ ν I : Type}

def vector (S : PartSelection n α κ) (ω : Fin n → α) (p : Fin n × κ) : ℝ :=
  S.value p.1 (ω p.1) p.2

theorem nonneg (S : PartSelection n α κ) (i : Fin n) (a : α) (j : κ) :
    0 ≤ S.value i a j := by
  rcases S.zero_one i a j with h | h <;> rw [h] <;> norm_num

theorem negatively_associated [Fintype α] [Nonempty α] [DecidableEq κ]
    (S : PartSelection n α κ) : NegAssociated S.vector := by
  apply negAssociated_independent_parts
  intro i
  exact one_hot_negAssociated (S.value i) (S.nonneg i) (S.at_most_one i)

def surviving (S : PartSelection n α κ) (T : PartSelection m β ν)
    (u : I → Fin n × κ) (v : I → Fin m × ν)
    (ω : (Fin n → α) × (Fin m → β)) (i : I) : ℝ :=
  S.vector ω.1 (u i) * T.vector ω.2 (v i)

theorem survival_zero_one (S : PartSelection n α κ) (T : PartSelection m β ν)
    (u : I → Fin n × κ) (v : I → Fin m × ν)
    (ω : (Fin n → α) × (Fin m → β)) (i : I) :
    S.surviving T u v ω i = 0 ∨ S.surviving T u v ω i = 1 := by
  rcases S.zero_one (u i).1 (ω.1 (u i).1) (u i).2 with h | h <;>
    rcases T.zero_one (v i).1 (ω.2 (v i).1) (v i).2 with h' | h' <;>
    simp [surviving, vector, h, h']

theorem survival_mean [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (S : PartSelection n α κ) (T : PartSelection m β ν)
    (u : I → Fin n × κ) (v : I → Fin m × ν) (i : I) :
    expectation (fun ω => S.surviving T u v ω i) =
      expectation (fun a => S.value (u i).1 a (u i).2) *
      expectation (fun b => T.value (v i).1 b (v i).2) := by
  unfold surviving vector
  rw [expectation_prod]
  simp_rw [expectation_const_mul]
  rw [expectation_mul_const,
    expectation_coordinate (u i).1 (fun a => S.value (u i).1 a (u i).2),
    expectation_coordinate (v i).1 (fun b => T.value (v i).1 b (v i).2)]

theorem matching_survival_tail [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [Fintype I] [DecidableEq I] [DecidableEq κ] [DecidableEq ν]
    (S : PartSelection n α κ) (T : PartSelection m β ν)
    (u : I → Fin n × κ) (v : I → Fin m × ν)
    (hu : Function.Injective u) (hv : Function.Injective v) :
    let μ := ∑ i, expectation (fun a => S.value (u i).1 a (u i).2) *
      expectation (fun b => T.value (v i).1 b (v i).2)
    prob (Finset.univ.filter (fun ω => (∑ i, S.surviving T u v ω i) ≤ μ / 2)) ≤
      Real.exp (-μ / 8) := by
  have hNA : NegAssociated (S.surviving T u v) :=
    negAssociated_matching_products S.vector T.vector S.negatively_associated T.negatively_associated
      (fun ω p => S.nonneg p.1 (ω p.1) p.2) (fun ω p => T.nonneg p.1 (ω p.1) p.2) u v hu hv
  have h := negAssociated_bernoulli_chernoff (S.surviving T u v) hNA (S.survival_zero_one T u v)
  simpa only [survival_mean] using h

theorem surviving_distinct_left_parts (S : PartSelection n α κ) (T : PartSelection m β ν)
    (u : I → Fin n × κ) (v : I → Fin m × ν) (hu : Function.Injective u)
    (ω : (Fin n → α) × (Fin m → β)) (i j : I) (hij : i ≠ j)
    (hi : S.surviving T u v ω i ≠ 0) (hj : S.surviving T u v ω j ≠ 0) :
    (u i).1 ≠ (u j).1 := by
  intro heq
  have h1 := (mul_ne_zero_iff.mp hi).1
  have h2 := (mul_ne_zero_iff.mp hj).1
  change S.value (u i).1 (ω.1 (u i).1) (u i).2 ≠ 0 at h1
  change S.value (u j).1 (ω.1 (u j).1) (u j).2 ≠ 0 at h2
  rw [← heq] at h2
  have hv := S.at_most_one _ _ _ _ h1 h2
  exact hij (hu (Prod.ext heq hv))

theorem surviving_distinct_right_parts (S : PartSelection n α κ) (T : PartSelection m β ν)
    (u : I → Fin n × κ) (v : I → Fin m × ν) (hv : Function.Injective v)
    (ω : (Fin n → α) × (Fin m → β)) (i j : I) (hij : i ≠ j)
    (hi : S.surviving T u v ω i ≠ 0) (hj : S.surviving T u v ω j ≠ 0) :
    (v i).1 ≠ (v j).1 := by
  intro heq
  have h1 := (mul_ne_zero_iff.mp hi).2
  have h2 := (mul_ne_zero_iff.mp hj).2
  change T.value (v i).1 (ω.2 (v i).1) (v i).2 ≠ 0 at h1
  change T.value (v j).1 (ω.2 (v j).1) (v j).2 ≠ 0 at h2
  rw [← heq] at h2
  have hu := T.at_most_one _ _ _ _ h1 h2
  exact hij (hv (Prod.ext heq hu))

end PartSelection

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.negAssociated_matching_products
#print axioms ChvatalErdos.FiniteProbability.PartSelection.matching_survival_tail
#print axioms ChvatalErdos.FiniteProbability.PartSelection.surviving_distinct_left_parts
#print axioms ChvatalErdos.FiniteProbability.PartSelection.surviving_distinct_right_parts
