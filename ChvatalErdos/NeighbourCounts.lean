import ChvatalErdos.CycleChoice
import ChvatalErdos.Chernoff

set_option autoImplicit false

namespace ChvatalErdos
open FiniteProbability CycleEndpoints
attribute [local instance] Classical.propDecidable

noncomputable def neighbourEvent {b l : Nat} (B : Finset (Fin b)) (j : Fin l) : Finset (Choice b l) :=
  Finset.univ.filter (fun c => entrance c ∈ B ∧ colour c = j)

theorem neighbourEvent_probability {b l : Nat} (hb : 0 < b) (hl : 0 < l)
    (B : Finset (Fin b)) (j : Fin l) :
    prob (neighbourEvent B j) = (B.card : ℝ) / ((b : ℝ) * l) := by
  have hmaps : ∀ c ∈ neighbourEvent B j, entrance c ∈ B :=
    fun c hc => (Finset.mem_filter.mp hc).2.1
  rw [prob_eq_sum_fibers entrance B _ hmaps]
  have hfiber : ∀ v ∈ B, (neighbourEvent B j).filter (fun c => entrance c = v) =
      Finset.univ.filter (fun c => entrance c = v ∧ colour c = j) := by
    intro v hv
    ext c
    simp only [neighbourEvent,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      exact ⟨h.2,h.1.2⟩
    · intro h
      exact ⟨⟨h.1 ▸ hv,h.2⟩,h.1⟩
  calc
    _ = ∑ _v ∈ B, 1 / ((b : ℝ) * l) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hfiber v hv,entrance_probability hb hl]
    _ = _ := by simp [div_eq_mul_inv]

theorem neighbour_tail {q b l : Nat} (hb : 0 < b) (hl : 0 < l)
    (B : Fin q → Finset (Fin b)) (j : Fin l) (d K : ℝ)
    (hK : 2 * (b : ℝ) ≤ K) (hd : K ≤ d)
    (hcount : d - b ≤ ∑ i : Fin q, ((B i).card : ℝ)) :
    prob (Finset.univ.filter (fun x : Fin q → Choice b l =>
      successCount (fun i => neighbourEvent (B i) j) x ≤ K / (4 * b * l))) ≤
      Real.exp (-d / (16 * b * l)) := by
  letI : NeZero b := ⟨hb.ne'⟩
  letI : NeZero l := ⟨hl.ne'⟩
  let A := fun i => neighbourEvent (B i) j
  let μ := totalMean A
  have hden : (0 : ℝ) < (b : ℝ) * l := mul_pos (by exact_mod_cast hb) (by exact_mod_cast hl)
  have hμ : μ = (∑ i : Fin q, ((B i).card : ℝ)) / ((b : ℝ) * l) := by
    dsimp [μ,totalMean,A]
    simp_rw [neighbourEvent_probability hb hl]
    simp only [div_eq_mul_inv,Finset.sum_mul]
  have hμlow : d / (2 * b * l) ≤ μ := by
    rw [hμ]
    have h : d / 2 ≤ ∑ i : Fin q, ((B i).card : ℝ) := by linarith
    have hh := div_le_div_of_nonneg_right h hden.le
    convert hh using 1 <;> ring
  have hthreshold : K / (4 * b * l) ≤ μ / 2 := by
    have hh := div_le_div_of_nonneg_right hμlow (by norm_num : (0 : ℝ) ≤ 2)
    have hdk := div_le_div_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ 4 * b * l)
    have heq : d / (2 * b * l) / 2 = d / (4 * b * l) := by ring
    rw [heq] at hh
    exact hdk.trans hh
  have ht := independent_chernoff A
  have hsub : Finset.univ.filter (fun x : Fin q → Choice b l => successCount A x ≤ K / (4 * b * l)) ⊆
      Finset.univ.filter (fun x => successCount A x ≤ μ / 2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hx).2).trans hthreshold⟩
  apply (prob_mono hsub).trans (ht.trans ?_)
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_right hμlow (by norm_num : (0 : ℝ) ≤ 8)
  have heq : d / (2 * b * l) / 8 = d / (16 * b * l) := by ring
  rw [heq] at h
  change -μ / 8 ≤ -d / (16 * b * l)
  simpa only [neg_div] using neg_le_neg h

theorem count_excluding_one_cycle {q b : Nat} (B : Fin q → Finset (Fin b)) (own : Fin q) :
    (∑ i : Fin q, ((B i).card : ℝ)) - b ≤
      ∑ i : Fin q, ((if i = own then ∅ else B i).card : ℝ) := by
  have hterm : ∀ i : Fin q, ((B i).card : ℝ) =
      ((if i = own then ∅ else B i).card : ℝ) + (if i = own then ((B own).card : ℝ) else 0) := by
    intro i
    by_cases h : i = own <;> simp [h]
  have heq := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hterm i)
  rw [Finset.sum_add_distrib] at heq
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at heq
  have hcard : ((B own).card : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (show (B own).card ≤ b by simpa using Finset.card_le_univ (B own))
  linarith

theorem neighbour_tail_excluding_own {q b l : Nat} (hb : 0 < b) (hl : 0 < l)
    (B : Fin q → Finset (Fin b)) (own : Fin q) (j : Fin l) (K : ℝ)
    (hK : 2 * (b : ℝ) ≤ K) (hd : K ≤ ∑ i : Fin q, ((B i).card : ℝ)) :
    prob (Finset.univ.filter (fun x : Fin q → Choice b l =>
      successCount (fun i => neighbourEvent (if i = own then ∅ else B i) j) x ≤ K / (4 * b * l))) ≤
      Real.exp (-(∑ i : Fin q, ((B i).card : ℝ)) / (16 * b * l)) :=
  neighbour_tail hb hl (fun i => if i = own then ∅ else B i) j _ K hK hd (count_excluding_one_cycle B own)

theorem prob_preimage_equiv {Ω Λ : Type} [Fintype Ω] [Fintype Λ] [DecidableEq Ω] [DecidableEq Λ]
    (e : Ω ≃ Λ) (P : Λ → Prop) :
    prob (Finset.univ.filter (fun x => P (e x))) = prob (Finset.univ.filter P) := by
  rw [← indicator_expectation,← indicator_expectation]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact expectation_equiv e (fun y => if P y then (1 : ℝ) else 0)

noncomputable def endpointTransport {b l : Nat} (hb : 4 ≤ b) : Equiv.Perm (Choice b l) where
  toFun c := (c.1,((if c.1 then shiftEquiv hb else (shiftEquiv hb).symm) c.2.1,c.2.2))
  invFun c := (c.1,((if c.1 then shiftEquiv hb else (shiftEquiv hb).symm).symm c.2.1,c.2.2))
  left_inv c := by cases c with | mk d p => cases p with | mk i j => cases d <;> simp
  right_inv c := by cases c with | mk d p => cases p with | mk i j => cases d <;> simp

noncomputable def exitNeighbourEvent {b l : Nat} (hb : 4 ≤ b) (B : Finset (Fin b)) (j : Fin l) :
    Finset (Choice b l) := Finset.univ.filter (fun c => exit hb c ∈ B ∧ colour c = j)

theorem exit_neighbour_tail {q b l : Nat} (hb : 4 ≤ b) (hl : 0 < l)
    (B : Fin q → Finset (Fin b)) (j : Fin l) (d K : ℝ)
    (hK : 2 * (b : ℝ) ≤ K) (hd : K ≤ d)
    (hcount : d - b ≤ ∑ i : Fin q, ((B i).card : ℝ)) :
    prob (Finset.univ.filter (fun x : Fin q → Choice b l =>
      successCount (fun i => exitNeighbourEvent hb (B i) j) x ≤ K / (4 * b * l))) ≤
      Real.exp (-d / (16 * b * l)) := by
  let e : Equiv.Perm (Fin q → Choice b l) := Equiv.piCongrRight (fun _ => endpointTransport hb)
  have heq : ∀ x : Fin q → Choice b l,
      successCount (fun i => exitNeighbourEvent hb (B i) j) x =
        successCount (fun i => neighbourEvent (B i) j) (e x) := by
    intro x
    apply Finset.sum_congr rfl
    intro i _
    have hmem : x i ∈ exitNeighbourEvent hb (B i) j ↔ e x i ∈ neighbourEvent (B i) j := by
      cases hdir : (x i).1 <;> simp [exitNeighbourEvent,neighbourEvent,e,endpointTransport,entrance,exit,colour,hdir]
    simp only [hmem]
  simp_rw [heq]
  rw [prob_preimage_equiv e (fun x => successCount (fun i => neighbourEvent (B i) j) x ≤ K / (4 * b * l))]
  exact neighbour_tail (by omega : 0 < b) hl B j d K hK hd hcount

end ChvatalErdos

#print axioms ChvatalErdos.neighbour_tail
#print axioms ChvatalErdos.neighbour_tail_excluding_own
#print axioms ChvatalErdos.exit_neighbour_tail
