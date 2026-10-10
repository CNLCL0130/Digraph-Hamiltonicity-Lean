import ChvatalErdos.NeighbourCounts
import ChvatalErdos.ConditionalFreeze

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open FiniteProbability CycleEndpoints

theorem stopped_success_tail {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    [DecidableEq I] [DecidableEq A] (T : QueryTree I A) (fixed : I → A)
    (events : I → Finset A) (hseen : ∀ i ∈ T.exposed fixed, events i = ∅)
    (threshold : ℝ) (hthreshold : threshold ≤ totalMean events / 2) :
    prob (Finset.univ.filter (fun x => successCount events x < threshold) ∩ historyEvent T fixed) /
      prob (historyEvent T fixed) ≤ Real.exp (-totalMean events / 8) := by
  rw [stopped_conditional_freeze]
  have he : ∀ x, successCount events (freeze (T.exposed fixed) fixed x) = successCount events x := by
    intro x
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ T.exposed fixed
    · simp [hseen i hi]
    · simp [freeze,hi]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  simp_rw [he]
  apply le_trans _ (independent_chernoff events)
  apply prob_mono
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hx).2).le.trans hthreshold⟩

variable {m b l : Nat}

noncomputable def directedNeighbourEvent (hb : 4 ≤ b) (outgoing : Bool)
    (B : Finset (Fin b)) (j : Fin l) : Finset (Choice b l) :=
  if outgoing then neighbourEvent B j else exitNeighbourEvent hb B j

theorem directedNeighbourEvent_probability (hb : 4 ≤ b) (hl : 0 < l) (outgoing : Bool)
    (B : Finset (Fin b)) (j : Fin l) :
    prob (directedNeighbourEvent hb outgoing B j) = (B.card : ℝ)/((b : ℝ)*l) := by
  cases outgoing with
  | true => exact neighbourEvent_probability (by omega) hl B j
  | false =>
    change prob (Finset.univ.filter (fun c => exit hb c ∈ B ∧ colour c = j)) = _
    let E := Finset.univ.filter (fun c : Choice b l => exit hb c ∈ B ∧ colour c = j)
    have hf : ∀ t ∈ B, E.filter (fun c => exit hb c = t) =
        Finset.univ.filter (fun c => exit hb c = t ∧ colour c = j) := by
      intro t ht
      ext c
      simp only [E,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro h; exact ⟨h.2,h.1.2⟩
      · intro h; exact ⟨⟨h.1 ▸ ht,h.2⟩,h.1⟩
    change prob E = _
    rw [prob_eq_sum_fibers (exit hb) B E (by intro c hc; exact (Finset.mem_filter.mp hc).2.1)]
    calc
      _ = ∑ _t ∈ B, 1/((b : ℝ)*l) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hf t ht,exit_probability hb hl]
      _ = _ := by simp [div_eq_mul_inv]

theorem stopped_neighbour_tail (hb : 4 ≤ b) (hl : 0 < l) (outgoing : Bool)
    (B : Fin m → Finset (Fin b)) (j : Fin l) (T : QueryTree (Fin m) (Choice b l))
    (fixed : Fin m → Choice b l) (hseen : ∀ i ∈ T.exposed fixed, B i = ∅)
    (K threshold : ℝ) (hcount : K/2 ≤ ∑ i, ((B i).card : ℝ))
    (hthreshold : threshold ≤ K/(4*b*l)) :
    prob (Finset.univ.filter (fun x =>
      successCount (fun i => directedNeighbourEvent hb outgoing (B i) j) x < threshold) ∩ historyEvent T fixed) /
      prob (historyEvent T fixed) ≤ Real.exp (-K/(16*b*l)) := by
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero l := ⟨hl.ne'⟩
  let events := fun i => directedNeighbourEvent hb outgoing (B i) j
  have hμ : totalMean events = (∑ i, ((B i).card : ℝ))/((b : ℝ)*l) := by
    dsimp [totalMean,events]
    simp_rw [directedNeighbourEvent_probability hb hl]
    simp only [div_eq_mul_inv,Finset.sum_mul]
  have hμlow : K/(2*b*l) ≤ totalMean events := by
    rw [hμ]
    have ht := div_le_div_of_nonneg_right hcount (by positivity : (0 : ℝ) ≤ (b : ℝ)*l)
    convert ht using 1 <;> ring
  have ht := stopped_success_tail T fixed events (by
    intro i hi
    dsimp [events,directedNeighbourEvent]
    rw [hseen i hi]
    cases outgoing <;> simp [neighbourEvent,exitNeighbourEvent]) threshold (by
      have hh := div_le_div_of_nonneg_right hμlow (by norm_num : (0 : ℝ) ≤ 2)
      have he : K/(2*b*l)/2 = K/(4*b*l) := by ring
      rw [he] at hh
      exact hthreshold.trans hh)
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right hμlow (by norm_num : (0 : ℝ) ≤ 8)
  have he : K/(2*b*l)/8 = K/(16*b*l) := by ring
  rw [he] at hh
  simpa only [neg_div] using neg_le_neg hh

end ChvatalErdos

#print axioms ChvatalErdos.stopped_neighbour_tail
