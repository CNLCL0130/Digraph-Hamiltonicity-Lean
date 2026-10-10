import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import ChvatalErdos.FiniteProbability

set_option autoImplicit false

namespace ChvatalErdos

/-- A deterministic adaptive examination of independent coordinates.
All parameters such as the record and the graph are fixed before choosing this tree.
A leaf can represent normal stopping, abort, or overflow.
-/
inductive QueryTree (ι α : Type) where
  | done : QueryTree ι α
  | ask (coordinate : ι) (next : α → QueryTree ι α) : QueryTree ι α

namespace QueryTree

variable {ι α : Type}

def transcript : QueryTree ι α → (ι → α) → List (ι × α)
  | .done, _ => []
  | .ask i next, x => (i, x i) :: transcript (next (x i)) x

/-- A bounded stateful algorithm with history-dependent queries determines a query tree.
The query and transition functions have no access to unqueried coordinates.
-/
def ofAlgorithm {σ : Type} (query : σ → Option ι)
    (advance : σ → ι → α → σ) : Nat → σ → QueryTree ι α
  | 0, _ => .done
  | n + 1, state => match query state with
    | none => .done
    | some i => .ask i (fun a => ofAlgorithm query advance n (advance state i a))

theorem transcript_sound (t : QueryTree ι α) (x : ι → α)
    (p : ι × α) (hp : p ∈ t.transcript x) : x p.1 = p.2 := by
  induction t with
  | done => simp [transcript] at hp
  | ask i next ih =>
    simp only [transcript, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact ih (x i) hp

/-- Every assignment agreeing with the complete transcript repeats that transcript. -/
theorem reproduce (t : QueryTree ι α) (x y : ι → α)
    (hagrees : ∀ p ∈ t.transcript x, y p.1 = p.2) :
    t.transcript y = t.transcript x := by
  induction t with
  | done => rfl
  | ask i next ih =>
    have hyi : y i = x i := hagrees (i, x i) (by simp [transcript])
    simp only [transcript, hyi]
    congr 1
    apply ih (x i)
    intro p hp
    exact hagrees p (by simp only [transcript, List.mem_cons]; exact Or.inr hp)

noncomputable def exposed [DecidableEq ι] (t : QueryTree ι α) (x : ι → α) : Finset ι :=
  (t.transcript x).map Prod.fst |>.toFinset

/-- The complete-history event is exactly a cylinder on its exposed coordinates. -/
theorem transcript_eq_iff_fixed [DecidableEq ι] (t : QueryTree ι α) (x y : ι → α) :
    t.transcript y = t.transcript x ↔ ∀ i ∈ t.exposed x, y i = x i := by
  constructor
  · intro h i hi
    simp only [exposed, List.mem_toFinset, List.mem_map] at hi
    obtain ⟨p, hp, hpi⟩ := hi
    subst i
    have hpy : p ∈ t.transcript y := by rw [h]; exact hp
    exact (transcript_sound t y p hpy).trans (transcript_sound t x p hp).symm
  · intro h
    apply reproduce t x y
    intro p hp
    have hi : p.1 ∈ t.exposed x := by
      simp only [exposed, List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩
    exact (h p.1 hi).trans (transcript_sound t x p hp)

end QueryTree

section ProductExperiment

variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

noncomputable def cylinder (s : Finset ι) (x : ι → α) : Finset (ι → α) :=
  Fintype.piFinset (fun i => if i ∈ s then {x i} else Finset.univ)

noncomputable def remainingEvent (s : Finset ι) (B : ι → Finset α) : Finset (ι → α) :=
  Fintype.piFinset (fun i => if i ∈ s then Finset.univ else B i)

noncomputable def conditionalFraction (A H : Finset (ι → α)) : ℝ :=
  ((A ∩ H).card : ℝ) / (H.card : ℝ)

omit [DecidableEq α] in
theorem mem_cylinder (s : Finset ι) (x y : ι → α) :
    y ∈ cylinder s x ↔ ∀ i ∈ s, y i = x i := by
  simp only [cylinder, Fintype.mem_piFinset]
  constructor
  · intro h i hi
    simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ s
    · simp [hi, h i hi]
    · simp [hi]

omit [DecidableEq α] in
theorem cylinder_nonempty (s : Finset ι) (x : ι → α) : (cylinder s x).Nonempty :=
  ⟨x, (mem_cylinder s x x).2 (fun _ _ => rfl)⟩

theorem cylinder_inter_remaining (s : Finset ι) (x : ι → α) (B : ι → Finset α) :
    remainingEvent s B ∩ cylinder s x =
      Fintype.piFinset (fun i => if i ∈ s then {x i} else B i) := by
  ext y
  simp only [Finset.mem_inter, cylinder, remainingEvent, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hb, hx⟩ i
    by_cases hi : i ∈ s
    · simpa [hi] using hx i
    · simpa [hi] using hb i
  · intro h
    constructor <;> intro i <;> by_cases hi : i ∈ s
    · simp [hi]
    · simpa [hi] using h i
    · simpa [hi] using h i
    · simp [hi]

/-- The exact finite conditional-product formula used after a stopping history. -/
theorem conditional_product (s : Finset ι) (x : ι → α) (B : ι → Finset α) :
    conditionalFraction (remainingEvent s B) (cylinder s x) =
      ∏ i : ι, if i ∈ s then 1 else (B i).card / (Fintype.card α : ℝ) := by
  unfold conditionalFraction
  rw [cylinder_inter_remaining]
  simp only [cylinder, Fintype.card_piFinset, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [hi]

noncomputable def historyEvent (t : QueryTree ι α) (x : ι → α) : Finset (ι → α) :=
  Finset.univ.filter (fun y => t.transcript y = t.transcript x)

theorem historyEvent_eq_cylinder (t : QueryTree ι α) (x : ι → α) :
    historyEvent t x = cylinder (t.exposed x) x := by
  ext y
  simp only [historyEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_cylinder, QueryTree.transcript_eq_iff_fixed]

/-- Conditioning on a realized adaptive transcript leaves all unexposed coordinates uniform
and independent. No condition on an unrelated good or bad event is added.
-/
theorem stopped_conditional_product (t : QueryTree ι α) (x : ι → α)
    (B : ι → Finset α) :
    conditionalFraction (remainingEvent (t.exposed x) B) (historyEvent t x) =
      ∏ i : ι, if i ∈ t.exposed x then 1 else (B i).card / (Fintype.card α : ℝ) := by
  rw [historyEvent_eq_cylinder]
  exact conditional_product (t.exposed x) x B

theorem history_probability_pos (t : QueryTree ι α) (x : ι → α) :
    0 < FiniteProbability.prob (historyEvent t x) := by
  letI : Nonempty (ι → α) := ⟨x⟩
  apply (FiniteProbability.prob_pos_iff _).2
  rw [historyEvent_eq_cylinder]
  exact cylinder_nonempty (t.exposed x) x

/-- The same statement using normalized probabilities, rather than cardinal ratios. -/
theorem stopped_conditional_probability (t : QueryTree ι α) (x : ι → α)
    (B : ι → Finset α) :
    FiniteProbability.prob (remainingEvent (t.exposed x) B ∩ historyEvent t x) /
      FiniteProbability.prob (historyEvent t x) =
      ∏ i : ι, if i ∈ t.exposed x then 1 else (B i).card / (Fintype.card α : ℝ) := by
  letI : Nonempty (ι → α) := ⟨x⟩
  have hH : (historyEvent t x).Nonempty := by
    rw [historyEvent_eq_cylinder]
    exact cylinder_nonempty (t.exposed x) x
  rw [FiniteProbability.conditional_eq_card_ratio _ _ hH]
  exact stopped_conditional_product t x B

/-- A single unexposed coordinate still has its original uniform law. -/
theorem fresh_coordinate_probability (t : QueryTree ι α) (x : ι → α)
    (q : ι) (hq : q ∉ t.exposed x) (B : Finset α) :
    FiniteProbability.prob (Finset.univ.filter (fun y : ι → α => y q ∈ B) ∩ historyEvent t x) /
      FiniteProbability.prob (historyEvent t x) = (B.card : ℝ) / Fintype.card α := by
  letI : Nonempty α := ⟨x q⟩
  let Bs : ι → Finset α := fun i => if i = q then B else Finset.univ
  have hevent : remainingEvent (t.exposed x) Bs =
      Finset.univ.filter (fun y : ι → α => y q ∈ B) := by
    ext y
    simp only [remainingEvent, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      simpa [Bs, hq] using h q
    · intro h i
      by_cases hi : i = q
      · subst i
        simp [Bs, hq, h]
      · by_cases hs : i ∈ t.exposed x <;> simp [Bs, hi, hs]
  rw [← hevent, stopped_conditional_probability]
  have hterm : ∀ i : ι,
      (if i ∈ t.exposed x then (1 : ℝ) else (Bs i).card / (Fintype.card α : ℝ)) =
      if i = q then (B.card : ℝ) / Fintype.card α else 1 := by
    intro i
    by_cases hi : i = q
    · subst i
      simp [hq, Bs]
    · by_cases hs : i ∈ t.exposed x <;> simp [hs, Bs, hi, Fintype.card_ne_zero]
  simp_rw [hterm]
  simp

theorem fresh_nonempty_event_lower_bound (t : QueryTree ι α) (x : ι → α)
    (q : ι) (hq : q ∉ t.exposed x) (B : Finset α) (hB : B.Nonempty) :
    1 / (Fintype.card α : ℝ) ≤
      FiniteProbability.prob (Finset.univ.filter (fun y : ι → α => y q ∈ B) ∩ historyEvent t x) /
        FiniteProbability.prob (historyEvent t x) := by
  rw [fresh_coordinate_probability t x q hq B]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.one_le_card.mpr hB

end ProductExperiment

end ChvatalErdos

#print axioms ChvatalErdos.QueryTree.transcript_eq_iff_fixed
#print axioms ChvatalErdos.stopped_conditional_product
#print axioms ChvatalErdos.stopped_conditional_probability
#print axioms ChvatalErdos.fresh_coordinate_probability
