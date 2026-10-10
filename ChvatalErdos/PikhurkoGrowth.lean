import ChvatalErdos.Remainder

set_option autoImplicit false

namespace ChvatalErdos.Pikhurko

theorem growth_constants (h δ : ℝ) (hh : 0 < h) (hδ : 16*h ≤ δ) :
    let ε := 4*h^2/δ
    0 ≤ ε ∧ ε ≤ h/4 ∧ ε*δ = 4*h^2 ∧
      0 < δ-6*h-ε ∧
      h^2 ≤ ε*(δ-6*h-ε) ∧
      δ*(h+ε) ≤ (δ-5*h-ε)*(h+4*ε) := by
  have hd : 0 < δ := by linarith
  dsimp
  let ε := 4*h^2/δ
  have he0 : 0 ≤ ε := by dsimp [ε]; positivity
  have heδ : ε*δ = 4*h^2 := by dsimp [ε]; field_simp
  have heh : ε ≤ h/4 := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_le_mul_of_nonneg_left hδ hh.le]
  have hhe := mul_nonneg hh.le (sub_nonneg.mpr heh)
  have hee := mul_nonneg he0 (sub_nonneg.mpr heh)
  refine ⟨he0,heh,heδ,by linarith,?_,?_⟩
  · nlinarith [heδ,hhe,hee,sq_nonneg h]
  · nlinarith [heδ,hhe,hee,sq_nonneg h]

theorem layer_step (h δ ε v w E : ℝ) (hh : 0 < h)
    (he0 : 0 ≤ ε) (hden : 0 < δ-6*h-ε)
    (hs : h^2 ≤ ε*(δ-6*h-ε))
    (hr : δ*(h+ε) ≤ (δ-5*h-ε)*(h+4*ε))
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hlower : (δ-5*h-ε)*v ≤ E) (hupper : E ≤ h*(v+w)) :
    E ≤ (h+ε)*w ∧ δ*v ≤ (h+4*ε)*w := by
  have hA : 0 < δ-5*h-ε := by linarith
  have hlo := mul_le_mul_of_nonneg_left hlower hh.le
  have hup := mul_le_mul_of_nonneg_left hupper hA.le
  have hsw := mul_le_mul_of_nonneg_right hs hw
  have hE : E ≤ (h+ε)*w := by
    apply (mul_le_mul_iff_left₀ hden).1
    nlinarith [hlo,hup,hsw]
  refine ⟨hE,?_⟩
  have hfactor : 0 < h+ε := by linarith
  have hlarge : 0 ≤ h+4*ε := by linarith
  have hlow' := mul_le_mul_of_nonneg_left hlower hlarge
  have hE' := mul_le_mul_of_nonneg_left hE hlarge
  have hrv := mul_le_mul_of_nonneg_right hr hv
  apply (mul_le_mul_iff_left₀ hfactor).1
  nlinarith [hlow',hE',hrv]

theorem layers_expand (k : Nat) (h δ : ℝ) (hh : 1 ≤ h) (hδ : 16*h ≤ δ)
    (v E : Nat → ℝ) (hv : ∀ i, 0 ≤ v i) (hv0 : v 0 = 1)
    (hE0 : E 0 = v 1) (hroot : δ ≤ v 1)
    (hlower : ∀ i, 1 ≤ i → i < k → (δ-4*h)*v i-E (i-1) ≤ E i)
    (hupper : ∀ i, 1 ≤ i → i < k → E i ≤ h*(v i+v (i+1))) :
    let ε := 4*h^2/δ
    (∀ i, i < k → E i ≤ (h+ε)*v (i+1)) ∧
    (δ/(h+4*ε))^k ≤ v k := by
  let ε := 4*h^2/δ
  obtain ⟨he0,heh,heδ,hden,hs,hr⟩ := growth_constants h δ (by linarith) hδ
  have hE : ∀ i, i < k → E i ≤ (h+ε)*v (i+1) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hE0]
      have hx := mul_nonneg (show 0 ≤ h+ε-1 by linarith) (hv 1)
      nlinarith
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hlow := hlower (i+1) (by omega) hi
      have heq : i+1-1 = i := by omega
      rw [heq] at hlow
      apply (layer_step h δ ε _ _ _ (by linarith) he0 hden hs hr (hv _) (hv _) ?_ (hupper _ (by omega) hi)).1
      nlinarith [hprev,hlow]
  have hstep : ∀ i, i < k → δ*v i ≤ (h+4*ε)*v (i+1) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [hv0,mul_one]
      have hx := mul_nonneg (show 0 ≤ h+4*ε-1 by linarith) (hv 1)
      nlinarith [hroot]
    · have hprev := hE (i-1) (by omega)
      have heq : i-1+1 = i := by omega
      rw [heq] at hprev
      have hlow := hlower i (by omega) hi
      exact (layer_step h δ ε _ _ _ (by linarith) he0 hden hs hr (hv _) (hv _)
        (by nlinarith [hprev,hlow]) (hupper i (by omega) hi)).2
  refine ⟨hE,?_⟩
  have hdpos : 0 < h+4*ε := by linarith
  have hratio : 0 ≤ δ/(h+4*ε) := div_nonneg (by linarith) hdpos.le
  have hpow : ∀ i, i ≤ k → (δ/(h+4*ε))^i ≤ v i := by
    intro i
    induction i with
    | zero => intro _; simp [hv0]
    | succ i ih =>
      intro hi
      rw [pow_succ]
      apply (mul_le_mul_of_nonneg_right (ih (by omega)) hratio).trans
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hdpos).2
      have hs' := hstep i (by omega)
      simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hs'
  exact hpow k le_rfl

theorem degree_bound_from_layers (k : Nat) (hk : 2 ≤ k) (N h δ : ℝ)
    (hN : 0 ≤ N) (hh : 1 ≤ h) (hδ : 16*h ≤ δ)
    (v E : Nat → ℝ) (hv : ∀ i, 0 ≤ v i) (hv0 : v 0 = 1)
    (hE0 : E 0 = v 1) (hroot : δ ≤ v 1) (hvN : v k ≤ N)
    (hlower : ∀ i, 1 ≤ i → i < k → (δ-4*h)*v i-E (i-1) ≤ E i)
    (hupper : ∀ i, 1 ≤ i → i < k → E i ≤ h*(v i+v (i+1))) :
    δ ≤ h*N^(1/(k : ℝ))+16*h := by
  let ε := 4*h^2/δ
  let q := N^(1/(k : ℝ))
  have hq : 0 ≤ q := Real.rpow_nonneg hN _
  have hqk : q^k = N := by
    dsimp [q]
    simpa only [one_div] using Real.rpow_inv_natCast_pow hN (by omega : k ≠ 0)
  obtain ⟨he0,heh,heδ,hden,hs,hr⟩ := growth_constants h δ (by linarith) hδ
  have hg := (layers_expand k h δ hh hδ v E hv hv0 hE0 hroot hlower hupper).2
  have hd : 0 < h+4*ε := by linarith
  have hratio : 0 ≤ δ/(h+4*ε) := div_nonneg (by linarith) hd.le
  have hrat : δ/(h+4*ε) ≤ q := by
    apply (pow_le_pow_iff_left₀ hratio hq (by omega : k ≠ 0)).1
    rw [hqk]
    exact hg.trans hvN
  have hδq : δ ≤ q*(h+4*ε) := (div_le_iff₀ hd).1 hrat
  by_cases hbase : δ ≤ h*q
  · change δ ≤ h*q+16*h
    linarith
  have hmul := mul_le_mul_of_nonneg_left (le_of_not_ge hbase) he0
  have heq : ε*q ≤ 4*h := by
    apply (mul_le_mul_iff_left₀ (by linarith : 0 < h)).1
    nlinarith [hmul,heδ]
  change δ ≤ h*q+16*h
  nlinarith [hδq,heq]

end ChvatalErdos.Pikhurko

#print axioms ChvatalErdos.Pikhurko.layer_step
#print axioms ChvatalErdos.Pikhurko.layers_expand
#print axioms ChvatalErdos.Pikhurko.degree_bound_from_layers
