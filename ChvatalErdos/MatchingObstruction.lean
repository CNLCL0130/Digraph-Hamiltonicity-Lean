import ChvatalErdos.CycleMatching
import ChvatalErdos.RecordSeparations

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints FiniteProbability
variable {n m b l r a : Nat}

theorem cycleMatchingValue_eq_one (hb : 4 ≤ b) (j : Fin l)
    (u v : Fin r → Fin m × Fin b) (x : Fin m → Choice b l) (e : Fin r) :
    cycleMatchingValue hb j u v x e = 1 ↔
      (exit hb (x (u e).1) = (u e).2 ∧ colour (x (u e).1) = j) ∧
      (entrance (x (v e).1) = (v e).2 ∧ colour (x (v e).1) = j) := by
  unfold cycleMatchingValue
  split <;> split <;> simp_all

/-- A compatible separation covers every surviving cross arc by its small
separator. Distinct surviving arcs require distinct separator vertices. -/
theorem Record.Separation.matching_count_lt (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (j : Fin l) (x : Fin m → Choice b l)
    (S : Record.Separation D Q hb a j x)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : Record.State n m) (hs : Record.Supported D Q s) (hcomp : S.Compatible s)
    (u v : Fin r → Fin m × Fin b) (hu : Function.Injective u) (hv : Function.Injective v)
    (hfreshu : ∀ e, (u e).1 ∉ s.seen) (hfreshv : ∀ e, (v e).1 ∉ s.seen)
    (hpureu : ∀ e t, Record.left D Q s (u e).1 t)
    (hpurev : ∀ e t, Record.right D Q s (v e).1 t)
    (harc : ∀ e, D.arc ((Q (u e).1).vertex (u e).2) ((Q (v e).1).vertex (v e).2)) :
    (∑ e, cycleMatchingValue hb j u v x e) < (a : ℝ) := by
  let F := Finset.univ.filter (fun e => cycleMatchingValue hb j u v x e = 1)
  have hmem : ∀ e ∈ F,
      (exit hb (x (u e).1) = (u e).2 ∧ colour (x (u e).1) = j) ∧
      (entrance (x (v e).1) = (v e).2 ∧ colour (x (v e).1) = j) := by
    intro e he
    exact (cycleMatchingValue_eq_one hb j u v x e).1 ((Finset.mem_filter.mp he).2)
  have hcross : ∀ e f, (u e).1 ≠ (v f).1 := by
    intro e f he
    have hleft := hpureu e ⟨0,by omega⟩
    have hright := hpurev f ⟨0,by omega⟩
    rw [he] at hleft
    exact left_right_exclusive D (· ∈ s.left) (· ∈ s.right) _ ⟨hleft,hright⟩
  have hleftinj : ∀ e ∈ F, ∀ f ∈ F, (u e).1 = (u f).1 → e = f := by
    intro e he f hf hef
    apply hu
    apply Prod.ext hef
    have h1 := (hmem e he).1.1
    have h2 := (hmem f hf).1.1
    rw [hef] at h1
    exact h1.symm.trans h2
  have hrightinj : ∀ e ∈ F, ∀ f ∈ F, (v e).1 = (v f).1 → e = f := by
    intro e he f hf hef
    apply hv
    apply Prod.ext hef
    have h1 := (hmem e he).2.1
    have h2 := (hmem f hf).2.1
    rw [hef] at h1
    exact h1.symm.trans h2
  have hcover : ∀ e ∈ F, (u e).1 ∈ S.X ∨ (v e).1 ∈ S.X := by
    intro e he
    have hm := hmem e he
    have hl := S.pure_left_forced hdis s hs hcomp (u e).1 (hfreshu e) (hpureu e) hm.1.2
    have hr := S.pure_right_forced hdis s hs hcomp (v e).1 (hfreshv e) (hpurev e) hm.2.2
    rcases hl with hl | hl
    · rcases hr with hr | hr
      · have hh := harc e
        rw [← hm.1.1,← hm.2.1] at hh
        exact (S.no_arc _ hl _ hr hh).elim
      · exact Or.inr hr
    · exact Or.inl hl
  let pick := fun e => if (u e).1 ∈ S.X then (u e).1 else (v e).1
  have hcard : F.card ≤ S.X.card := by
    apply Finset.card_le_card_of_injOn pick
    · intro e he
      dsimp [pick]
      split
      · assumption
      · exact (hcover e he).resolve_left (by assumption)
    · intro e he f hf heq
      dsimp [pick] at heq
      split at heq <;> split at heq
      · exact hleftinj e he f hf heq
      · exact (hcross e f heq).elim
      · exact (hcross f e heq.symm).elim
      · exact hrightinj e he f hf heq
  have hsum : (∑ e, cycleMatchingValue hb j u v x e) = (F.card : ℝ) := by
    have hval : ∀ e, cycleMatchingValue hb j u v x e = if e ∈ F then (1 : ℝ) else 0 := by
      intro e
      simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
      unfold cycleMatchingValue
      split <;> split <;> norm_num
    simp_rw [hval]
    simp
  rw [hsum]
  exact_mod_cast (lt_of_le_of_lt hcard S.small)

noncomputable def Record.compatibleEvent (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (a : Nat) (j : Fin l) (s : Record.State n m) : Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x => ∃ S : Record.Separation D Q hb a j x, S.Compatible s)

theorem stopped_matching_obstruction_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : Record.State n m) (hs : Record.Supported D Q s)
    (u v : Fin r → Fin m × Fin b) (hu : Function.Injective u) (hv : Function.Injective v)
    (hfreshu : ∀ e, (u e).1 ∉ s.seen) (hfreshv : ∀ e, (v e).1 ∉ s.seen)
    (hpureu : ∀ e t, Record.left D Q s (u e).1 t)
    (hpurev : ∀ e t, Record.right D Q s (v e).1 t)
    (harc : ∀ e, D.arc ((Q (u e).1).vertex (u e).2) ((Q (v e).1).vertex (v e).2))
    (T : QueryTree (Fin m) (Choice b l)) (fixed : Fin m → Choice b l)
    (hseen : s.seen = T.exposed fixed) (hbudget : (a : ℝ) ≤ (r : ℝ)/(2*b^2*l^2)) :
    prob (Record.compatibleEvent D Q hb a j s ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤
      Real.exp (-(r : ℝ)/(8*b^2*l^2)) := by
  let side : Fin m → Bool := fun i => decide (∀ t, Record.left D Q s i t)
  have hsideu : ∀ e, side (u e).1 = true := by intro e; simp [side,hpureu e]
  have hsidev : ∀ e, side (v e).1 = false := by
    intro e
    have hn : ¬∀ t, Record.left D Q s (v e).1 t := by
      intro hh
      exact left_right_exclusive D (· ∈ s.left) (· ∈ s.right) _
        ⟨hh ⟨0,by omega⟩,hpurev e ⟨0,by omega⟩⟩
    simp [side,hn]
  have ht := stopped_cycleMatching_tail hb hl j side u v hu hv hsideu hsidev T fixed
    (by intro e; rw [← hseen]; exact hfreshu e) (by intro e; rw [← hseen]; exact hfreshv e)
  apply le_trans _ ht
  apply div_le_div_of_nonneg_right _ (prob_nonneg _)
  apply prob_mono
  intro x hx
  obtain ⟨S,hS⟩ := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
  refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,(Finset.mem_inter.mp hx).2⟩
  exact (S.matching_count_lt D Q hb j x hdis s hs hS u v hu hv hfreshu hfreshv hpureu hpurev harc).le.trans hbudget

end ChvatalErdos

#print axioms ChvatalErdos.Record.Separation.matching_count_lt
#print axioms ChvatalErdos.stopped_matching_obstruction_tail
