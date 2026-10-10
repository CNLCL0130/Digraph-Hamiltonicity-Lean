import ChvatalErdos.MatchingSurvival
import ChvatalErdos.CycleChoice
import ChvatalErdos.ConditionalFreeze

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open FiniteProbability CycleEndpoints

theorem expectation_two_coordinates {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    [DecidableEq I] [DecidableEq A] (i j : I) (hij : i ≠ j) (f g : A → ℝ) :
    expectation (fun x : I → A => f (x i) * g (x j)) = expectation f * expectation g := by
  rw [expectation_coordinate_update _ i]
  simp only [Function.update_self,Function.update_of_ne hij.symm]
  simp_rw [expectation_const_mul,expectation_coordinate,expectation_mul_const]

variable {m b l r : Nat}

noncomputable def endpointSelection (hb : 4 ≤ b) (side : Fin m → Bool) (j : Fin l) :
    PartSelection m (Choice b l) (Fin b) where
  value i c t := if colour c = j ∧ (if side i then exit hb c else entrance c) = t then 1 else 0
  zero_one i c t := by
    by_cases h : colour c = j ∧ (if side i then exit hb c else entrance c) = t <;> simp [h]
  at_most_one i c t u ht hu := by
    have h : colour c = j ∧ (if side i then exit hb c else entrance c) = t := by
      by_contra hn
      simp [hn] at ht
    have h' : colour c = j ∧ (if side i then exit hb c else entrance c) = u := by
      by_contra hn
      simp [hn] at hu
    exact h.2.symm.trans h'.2

theorem endpointSelection_mean (hb : 4 ≤ b) (hl : 0 < l) (side : Fin m → Bool)
    (j : Fin l) (i : Fin m) (t : Fin b) :
    expectation (fun c => (endpointSelection hb side j).value i c t) = 1/((b : ℝ)*l) := by
  have hp : ∀ (endpoint : Choice b l → Fin b),
      expectation (fun c => if colour c = j ∧ endpoint c = t then (1 : ℝ) else 0) =
      prob (Finset.univ.filter (fun c => endpoint c = t ∧ colour c = j)) := by
    intro endpoint
    rw [← indicator_expectation]
    simp [and_comm]
  change expectation (fun c => if colour c = j ∧ (if side i then exit hb c else entrance c) = t then (1 : ℝ) else 0) = _
  cases hs : side i
  · simp only [Bool.false_eq_true,if_false]
    exact (hp entrance).trans (entrance_probability (by omega) hl t j)
  · simp only [if_true]
    exact (hp (exit hb)).trans (exit_probability hb hl t j)

noncomputable def cycleMatchingValue (hb : 4 ≤ b) (j : Fin l)
    (u v : Fin r → Fin m × Fin b) (x : Fin m → Choice b l) (e : Fin r) : ℝ :=
  (if exit hb (x (u e).1) = (u e).2 ∧ colour (x (u e).1) = j then 1 else 0) *
  (if entrance (x (v e).1) = (v e).2 ∧ colour (x (v e).1) = j then 1 else 0)

theorem cycleMatching_tail (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l)
    (side : Fin m → Bool) (u v : Fin r → Fin m × Fin b)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsideu : ∀ e, side (u e).1 = true) (hsidev : ∀ e, side (v e).1 = false) :
    prob (Finset.univ.filter (fun x : Fin m → Choice b l =>
      (∑ e, cycleMatchingValue hb j u v x e) ≤ (r : ℝ)/(2*b^2*l^2))) ≤
      Real.exp (-(r : ℝ)/(8*b^2*l^2)) := by
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero l := ⟨hl.ne'⟩
  let S := endpointSelection hb side j
  have huv : ∀ e f, (u e).1 ≠ (v f).1 := by
    intro e f he
    have h := hsideu e
    rw [he,hsidev] at h
    contradiction
  let support : Fin r → Finset (Fin m × Fin b) := fun e => {u e,v e}
  have hdis : ∀ e f, e ≠ f → Disjoint (support e) (support f) := by
    intro e f hef
    apply Finset.disjoint_left.mpr
    intro t hte htf
    simp only [support,Finset.mem_insert,Finset.mem_singleton] at hte htf
    rcases hte with hte | hte <;> rcases htf with htf | htf
    · exact hef (hu (hte.symm.trans htf))
    · exact huv e f (congrArg Prod.fst (hte.symm.trans htf))
    · exact huv f e (congrArg Prod.fst (htf.symm.trans hte))
    · exact hef (hv (hte.symm.trans htf))
  let φ : Fin r → (Fin m × Fin b → ℝ) → ℝ := fun e z => max 0 (z (u e)) * max 0 (z (v e))
  have hmono : ∀ e, Monotone (φ e) := by
    intro e x y hxy
    exact mul_le_mul (max_le_max le_rfl (hxy _)) (max_le_max le_rfl (hxy _))
      (le_max_left _ _) (le_max_left _ _)
  have hdep : ∀ e, FiniteProbability.DependsOn (φ e) (support e) := by
    intro e x y hxy
    dsimp [φ]
    rw [hxy (u e) (by simp [support]),hxy (v e) (by simp [support])]
  have hvalue : ∀ x e, φ e (S.vector x) = cycleMatchingValue hb j u v x e := by
    intro x e
    change max 0 (S.value (u e).1 (x (u e).1) (u e).2) *
      max 0 (S.value (v e).1 (x (v e).1) (v e).2) = _
    rw [max_eq_right (S.nonneg _ _ _),max_eq_right (S.nonneg _ _ _)]
    simp [S,endpointSelection,PartSelection.vector,cycleMatchingValue,hsideu,hsidev,and_comm]
  have hNA : NegAssociated (cycleMatchingValue hb j u v) := by
    have hh := negAssociated_disjoint_maps S.vector S.negatively_associated support hdis φ hmono hdep
    simpa only [hvalue] using hh
  have h01 : ∀ x e, cycleMatchingValue hb j u v x e = 0 ∨ cycleMatchingValue hb j u v x e = 1 := by
    intro x e
    unfold cycleMatchingValue
    split <;> split <;> norm_num
  have hmean : ∀ e, expectation (fun x => cycleMatchingValue hb j u v x e) = 1/((b : ℝ)^2*l^2) := by
    intro e
    have hfactor := expectation_two_coordinates (u e).1 (v e).1 (huv e e)
      (fun c => S.value (u e).1 c (u e).2) (fun c => S.value (v e).1 c (v e).2)
    have hval : ∀ x, cycleMatchingValue hb j u v x e =
        S.value (u e).1 (x (u e).1) (u e).2 * S.value (v e).1 (x (v e).1) (v e).2 := by
      intro x
      simp [S,endpointSelection,cycleMatchingValue,hsideu,hsidev,and_comm]
    simp_rw [hval]
    rw [hfactor,endpointSelection_mean hb hl,endpointSelection_mean hb hl]
    ring
  have ht := negAssociated_bernoulli_chernoff (cycleMatchingValue hb j u v) hNA h01
  simp_rw [hmean] at ht
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at ht
  have he1 : (r : ℝ)*(1/((b : ℝ)^2*l^2))/2 = (r : ℝ)/(2*b^2*l^2) := by ring
  have he2 : -((r : ℝ)*(1/((b : ℝ)^2*l^2)))/8 = -(r : ℝ)/(8*b^2*l^2) := by ring
  rwa [he1,he2] at ht

/-- The matching tail remains valid conditioned on a complete query history,
provided every endpoint lies on an unexposed cycle. -/
theorem stopped_cycleMatching_tail (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l)
    (side : Fin m → Bool) (u v : Fin r → Fin m × Fin b)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsideu : ∀ e, side (u e).1 = true) (hsidev : ∀ e, side (v e).1 = false)
    (T : QueryTree (Fin m) (Choice b l)) (fixed : Fin m → Choice b l)
    (hfreshu : ∀ e, (u e).1 ∉ T.exposed fixed) (hfreshv : ∀ e, (v e).1 ∉ T.exposed fixed) :
    prob (Finset.univ.filter (fun x : Fin m → Choice b l =>
      (∑ e, cycleMatchingValue hb j u v x e) ≤ (r : ℝ)/(2*b^2*l^2)) ∩ historyEvent T fixed) /
      prob (historyEvent T fixed) ≤ Real.exp (-(r : ℝ)/(8*b^2*l^2)) := by
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero l := ⟨hl.ne'⟩
  rw [stopped_conditional_freeze]
  have he : ∀ x e, cycleMatchingValue hb j u v (freeze (T.exposed fixed) fixed x) e =
      cycleMatchingValue hb j u v x e := by
    intro x e
    simp [cycleMatchingValue,freeze,hfreshu,hfreshv]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  simp_rw [he]
  exact cycleMatching_tail hb hl j side u v hu hv hsideu hsidev

end ChvatalErdos

#print axioms ChvatalErdos.cycleMatching_tail
#print axioms ChvatalErdos.stopped_cycleMatching_tail
