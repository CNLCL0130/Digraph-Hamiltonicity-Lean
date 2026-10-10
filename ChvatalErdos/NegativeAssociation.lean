import ChvatalErdos.Chernoff

set_option autoImplicit false

namespace ChvatalErdos.FiniteProbability

variable {Ω ι : Type} [Fintype Ω] [Nonempty Ω]

def DependsOn (f : (ι → ℝ) → ℝ) (s : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

def NegAssociated (X : Ω → ι → ℝ) : Prop :=
  ∀ s t : Finset ι, Disjoint s t →
    ∀ f g : (ι → ℝ) → ℝ, Monotone f → Monotone g →
      DependsOn f s → DependsOn g t →
      expectation (fun ω => f (X ω) * g (X ω)) ≤
        expectation (fun ω => f (X ω)) * expectation (fun ω => g (X ω))

omit [Nonempty Ω] in
theorem expectation_add (f g : Ω → ℝ) :
    expectation (fun ω => f ω + g ω) = expectation f + expectation g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

/-- This covariance lemma is the algebraic reason a one-hot vector is negatively associated. -/
theorem exclusive_covariance (F G : Ω → ℝ) (c d : ℝ)
    (hF : ∀ ω, c ≤ F ω) (hG : ∀ ω, d ≤ G ω)
    (hexclusive : ∀ ω, F ω = c ∨ G ω = d) :
    expectation (fun ω => F ω * G ω) ≤ expectation F * expectation G := by
  have hpoint : (fun ω => F ω * G ω) =
      (fun ω => c * G ω + F ω * d - c * d) := by
    funext ω
    rcases hexclusive ω with h | h <;> rw [h] <;> ring
  have hEF : c ≤ expectation F := by
    simpa only [expectation_const] using expectation_mono hF
  have hEG : d ≤ expectation G := by
    simpa only [expectation_const] using expectation_mono hG
  rw [hpoint, expectation_sub, expectation_add, expectation_const_mul,
    expectation_mul_const, expectation_const]
  nlinarith [mul_nonneg (sub_nonneg.mpr hEF) (sub_nonneg.mpr hEG)]

/-- No assumption of independence inside a part: it can select at most one coordinate. -/
theorem one_hot_negAssociated (X : Ω → ι → ℝ)
    (hnonneg : ∀ ω i, 0 ≤ X ω i)
    (hone : ∀ ω i j, X ω i ≠ 0 → X ω j ≠ 0 → i = j) : NegAssociated X := by
  intro s t hst f g hf hg hfs hgt
  apply exclusive_covariance _ _ (f 0) (g 0)
  · intro ω
    exact hf (hnonneg ω)
  · intro ω
    exact hg (hnonneg ω)
  · intro ω
    classical
    by_cases hs : ∀ i ∈ s, X ω i = 0
    · exact Or.inl (hfs _ _ hs)
    · push_neg at hs
      obtain ⟨i, hi, hxi⟩ := hs
      apply Or.inr
      apply hgt
      intro j hj
      by_contra hxj
      have hij := hone ω i j hxi hxj
      exact Finset.disjoint_left.mp hst hi (hij ▸ hj)

omit [Nonempty Ω] in
theorem negAssociated_antitone (X : Ω → ι → ℝ) (hX : NegAssociated X)
    (s t : Finset ι) (hst : Disjoint s t) (f g : (ι → ℝ) → ℝ)
    (hf : Antitone f) (hg : Antitone g) (hfs : DependsOn f s) (hgt : DependsOn g t) :
    expectation (fun ω => f (X ω) * g (X ω)) ≤
      expectation (fun ω => f (X ω)) * expectation (fun ω => g (X ω)) := by
  have h := hX s t hst (fun x => -f x) (fun x => -g x)
    (fun _ _ hxy => neg_le_neg (hf hxy)) (fun _ _ hxy => neg_le_neg (hg hxy))
    (fun x y hxy => congrArg Neg.neg (hfs x y hxy))
    (fun x y hxy => congrArg Neg.neg (hgt x y hxy))
  have hneg : ∀ F : Ω → ℝ, expectation (fun ω => -F ω) = -expectation F := by
    intro F
    simp [expectation, Finset.sum_neg_distrib, neg_div]
  simpa only [neg_mul_neg, hneg] using h

theorem negAssociated_prod_le [DecidableEq ι] (X : Ω → ι → ℝ) (hX : NegAssociated X)
    (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i, Antitone (f i))
    (hpos : ∀ i x, 0 ≤ f i x) :
    expectation (fun ω => ∏ i ∈ s, f i (X ω i)) ≤
      ∏ i ∈ s, expectation (fun ω => f i (X ω i)) := by
  induction s using Finset.induction_on with
  | empty => simp [expectation_const]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    have hdis : Disjoint ({i} : Finset ι) s := by simpa using hi
    have hanti : Antitone (fun x : ι → ℝ => ∏ j ∈ s, f j (x j)) := by
      intro x y hxy
      exact Finset.prod_le_prod (fun j _ => hpos j (y j)) (fun j _ => hf j (hxy j))
    have hdep : DependsOn (fun x : ι → ℝ => ∏ j ∈ s, f j (x j)) s := by
      intro x y hxy
      exact Finset.prod_congr rfl (fun j hj => congrArg (f j) (hxy j hj))
    have hna := negAssociated_antitone X hX {i} s hdis
      (fun x => f i (x i)) (fun x => ∏ j ∈ s, f j (x j))
      (fun _ _ hxy => hf i (hxy i)) hanti
      (fun x y hxy => congrArg (f i) (hxy i (Finset.mem_singleton_self i))) hdep
    apply hna.trans
    apply mul_le_mul_of_nonneg_left ih
    simpa only [expectation_const] using
      (expectation_mono (fun ω => hpos i (X ω i)))

omit [Nonempty Ω] in
theorem negAssociated_disjoint_maps {κ : Type} [DecidableEq ι] [DecidableEq κ]
    (X : Ω → ι → ℝ) (hX : NegAssociated X)
    (support : κ → Finset ι) (hdis : ∀ i j, i ≠ j → Disjoint (support i) (support j))
    (φ : κ → (ι → ℝ) → ℝ) (hmono : ∀ i, Monotone (φ i))
    (hdep : ∀ i, DependsOn (φ i) (support i)) :
    NegAssociated (fun ω i => φ i (X ω)) := by
  intro s t hst f g hf hg hfs hgt
  have hd : Disjoint (s.biUnion support) (t.biUnion support) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hw
    have hij : i ≠ j := by
      intro heq
      subst j
      exact Finset.disjoint_left.mp hst hi hj
    exact Finset.disjoint_left.mp (hdis i j hij) hvi hvj
  apply hX (s.biUnion support) (t.biUnion support) hd
    (fun x => f (fun i => φ i x)) (fun x => g (fun i => φ i x))
  · intro x y hxy
    exact hf (fun i => hmono i hxy)
  · intro x y hxy
    exact hg (fun i => hmono i hxy)
  · intro x y hxy
    apply hfs
    intro i hi
    apply hdep i
    intro v hv
    exact hxy v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
  · intro x y hxy
    apply hgt
    intro i hi
    apply hdep i
    intro v hv
    exact hxy v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)

omit [Nonempty Ω] in
theorem negAssociated_independent_sum {Λ κ : Type} [Fintype Λ]
    (X : Ω → ι → ℝ) (Y : Λ → κ → ℝ)
    (hX : NegAssociated X) (hY : NegAssociated Y) :
    NegAssociated (fun ω : Ω × Λ => Sum.elim (X ω.1) (Y ω.2)) := by
  intro s t hst f g hf hg hfs hgt
  have hleft : Disjoint s.toLeft t.toLeft := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hst (Finset.mem_toLeft.mp hi) (Finset.mem_toLeft.mp hj)
  have hright : Disjoint s.toRight t.toRight := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hst (Finset.mem_toRight.mp hi) (Finset.mem_toRight.mp hj)
  have slice_mono : ∀ (f : (ι ⊕ κ → ℝ) → ℝ), Monotone f → ∀ x : ι → ℝ,
      Monotone (fun y : κ → ℝ => f (Sum.elim x y)) := by
    intro f hf x y z hyz
    apply hf
    intro i
    cases i with
    | inl i => exact le_rfl
    | inr i => exact hyz i
  have slice_dep : ∀ (f : (ι ⊕ κ → ℝ) → ℝ) (s : Finset (ι ⊕ κ)), DependsOn f s →
      ∀ x : ι → ℝ, DependsOn (fun y : κ → ℝ => f (Sum.elim x y)) s.toRight := by
    intro f s hdep x y z hyz
    apply hdep
    intro i hi
    cases i with
    | inl i => rfl
    | inr i => exact hyz i (Finset.mem_toRight.mpr hi)
  let F : (ι → ℝ) → ℝ := fun x => expectation (fun zeta => f (Sum.elim x (Y zeta)))
  let G : (ι → ℝ) → ℝ := fun x => expectation (fun zeta => g (Sum.elim x (Y zeta)))
  have avg_mono : ∀ (f : (ι ⊕ κ → ℝ) → ℝ), Monotone f →
      Monotone (fun x : ι → ℝ => expectation (fun zeta => f (Sum.elim x (Y zeta)))) := by
    intro f hf x z hxz
    apply expectation_mono
    intro zeta
    apply hf
    intro i
    cases i with
    | inl i => exact hxz i
    | inr i => exact le_rfl
  have avg_dep : ∀ (f : (ι ⊕ κ → ℝ) → ℝ) (s : Finset (ι ⊕ κ)), DependsOn f s →
      DependsOn (fun x : ι → ℝ => expectation (fun zeta => f (Sum.elim x (Y zeta)))) s.toLeft := by
    intro f s hdep x z hxz
    apply congrArg expectation
    funext zeta
    apply hdep
    intro i hi
    cases i with
    | inl i => exact hxz i (Finset.mem_toLeft.mpr hi)
    | inr i => rfl
  simp only [expectation_prod]
  calc
    _ ≤ expectation (fun ω => F (X ω) * G (X ω)) := by
      apply expectation_mono
      intro ω
      exact hY s.toRight t.toRight hright _ _ (slice_mono f hf (X ω))
        (slice_mono g hg (X ω)) (slice_dep f s hfs (X ω)) (slice_dep g t hgt (X ω))
    _ ≤ _ := hX s.toLeft t.toLeft hleft F G (avg_mono f hf) (avg_mono g hg)
      (avg_dep f s hfs) (avg_dep g t hgt)

omit [Nonempty Ω] in
theorem negAssociated_reindex {κ : Type} [DecidableEq ι] [DecidableEq κ]
    (X : Ω → ι → ℝ) (hX : NegAssociated X) (e : κ → ι) (he : Function.Injective e) :
    NegAssociated (fun ω i => X ω (e i)) := by
  refine negAssociated_disjoint_maps X hX (fun i => {e i}) ?_
    (fun i x => x (e i)) ?_ ?_
  · intro i j hij
    simpa using fun h => hij (he h.symm)
  · intro i x y hxy
    exact hxy (e i)
  · intro i x y hxy
    exact hxy (e i) (Finset.mem_singleton_self _)

omit [Nonempty Ω] in
theorem negAssociated_sample_equiv {Λ : Type} [Fintype Λ]
    (X : Ω → ι → ℝ) (hX : NegAssociated X) (e : Λ ≃ Ω) :
    NegAssociated (fun z => X (e z)) := by
  intro s t hst f g hf hg hfs hgt
  rw [expectation_equiv e (fun ω => f (X ω) * g (X ω)),
    expectation_equiv e (fun ω => f (X ω)), expectation_equiv e (fun ω => g (X ω))]
  exact hX s t hst f g hf hg hfs hgt

def splitPart {κ : Type} (n : Nat) (p : Fin (n + 1) × κ) : κ ⊕ (Fin n × κ) :=
  Fin.cases (Sum.inl p.2) (fun i => Sum.inr (i, p.2)) p.1

theorem splitPart_injective {κ : Type} (n : Nat) : Function.Injective (@splitPart κ n) := by
  intro ⟨i, j⟩ ⟨k, l⟩ h
  cases i using Fin.cases <;> cases k using Fin.cases <;> simp_all [splitPart]

theorem negAssociated_independent_parts {α κ : Type} [Fintype α] [Nonempty α]
    [DecidableEq κ] (n : Nat) (X : Fin n → α → κ → ℝ)
    (hX : ∀ i, NegAssociated (X i)) :
    NegAssociated (fun ω : Fin n → α => fun p : Fin n × κ => X p.1 (ω p.1) p.2) := by
  induction n with
  | zero =>
    intro s t hst f g hf hg hfs hgt
    have hconstant : ∀ ω : Fin 0 → α, (fun p : Fin 0 × κ => X p.1 (ω p.1) p.2) = 0 := by
      intro ω
      funext p
      exact Fin.elim0 p.1
    simp only [hconstant, expectation_const, le_refl]
  | succ n ih =>
    let tailX := fun i : Fin n => X i.succ
    have htail := ih tailX (fun i => hX i.succ)
    have hsum := negAssociated_independent_sum (X 0)
      (fun ω : Fin n → α => fun p : Fin n × κ => tailX p.1 (ω p.1) p.2) (hX 0) htail
    have hsample := negAssociated_sample_equiv _ hsum (Fin.consEquiv (fun _ : Fin (n+1) => α)).symm
    have hcoord := negAssociated_reindex _ hsample (splitPart n) (splitPart_injective n)
    convert hcoord using 1
    funext ω p
    rcases p with ⟨i,j⟩
    cases i using Fin.cases <;> simp [splitPart, tailX, Fin.consEquiv, Fin.tail]

theorem negAssociated_bernoulli_chernoff [Fintype ι] [DecidableEq ι]
    (X : Ω → ι → ℝ) (hX : NegAssociated X)
    (h01 : ∀ ω i, X ω i = 0 ∨ X ω i = 1) :
    let μ := ∑ i, expectation (fun ω => X ω i)
    prob (Finset.univ.filter (fun ω => (∑ i, X ω i) ≤ μ / 2)) ≤ Real.exp (-μ / 8) := by
  classical
  dsimp only
  have hnonneg : ∀ ω i, 0 ≤ X ω i := by
    intro ω i
    rcases h01 ω i with h | h <;> rw [h] <;> norm_num
  have hEpos : ∀ i, 0 ≤ expectation (fun ω => X ω i) := by
    intro i
    simpa only [expectation_const] using expectation_mono (fun ω => hnonneg ω i)
  have hEone : ∀ i, expectation (fun ω => X ω i) ≤ 1 := by
    intro i
    have hle : ∀ ω, X ω i ≤ 1 := by
      intro ω
      rcases h01 ω i with h | h <;> rw [h] <;> norm_num
    simpa only [expectation_const] using expectation_mono hle
  have hmoment : ∀ i, expectation (fun ω => Real.exp (-Real.log 2 * X ω i)) =
      1 - expectation (fun ω => X ω i) / 2 := by
    intro i
    have heq : (fun ω => Real.exp (-Real.log 2 * X ω i)) = (fun ω => 1 - X ω i / 2) := by
      funext ω
      rcases h01 ω i with h | h <;>
        simp [h, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] <;> norm_num
    rw [heq, expectation_sub, expectation_const, expectation_div]
  apply lower_tail_of_laplace _ _ (Finset.sum_nonneg (fun i _ => hEpos i))
  have hfactor := negAssociated_prod_le X hX Finset.univ
    (fun _ x => Real.exp (-Real.log 2 * x))
    (fun _ _ _ hxy => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy
      (neg_nonpos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)))
    (fun _ _ => (Real.exp_pos _).le)
  have heq : (fun ω => Real.exp (-Real.log 2 * ∑ i, X ω i)) =
      (fun ω => ∏ i, Real.exp (-Real.log 2 * X ω i)) := by
    funext ω
    rw [Finset.mul_sum, Real.exp_sum]
  rw [heq]
  apply hfactor.trans
  simp_rw [hmoment]
  calc
    _ ≤ ∏ i, Real.exp (-expectation (fun ω => X ω i) / 2) := by
      apply Finset.prod_le_prod
      · intro i _
        linarith [hEone i]
      · intro i _
        linarith [Real.add_one_le_exp (-expectation (fun ω => X ω i) / 2)]
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [div_eq_mul_inv, Finset.sum_neg_distrib, ← Finset.sum_mul, neg_mul]

end ChvatalErdos.FiniteProbability

#print axioms ChvatalErdos.FiniteProbability.one_hot_negAssociated
#print axioms ChvatalErdos.FiniteProbability.negAssociated_prod_le
#print axioms ChvatalErdos.FiniteProbability.negAssociated_disjoint_maps
#print axioms ChvatalErdos.FiniteProbability.negAssociated_independent_sum
#print axioms ChvatalErdos.FiniteProbability.negAssociated_independent_parts
#print axioms ChvatalErdos.FiniteProbability.negAssociated_bernoulli_chernoff
