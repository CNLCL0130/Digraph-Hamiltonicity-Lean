import ChvatalErdos.NormalStopBound
import ChvatalErdos.RecordOverflow
import ChvatalErdos.RecordWords

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints FiniteProbability
variable {n m b l a w : Nat}

def Normal (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (N : Nat) (s : State n m) : Prop :=
  s.aborted = false ∧ s.seen.card < N ∧ mixed D Q s = ∅

noncomputable def normalBad (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) : Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x =>
    Normal D Q N (stateAfter D Q hb a N j word N x) ∧
    ∃ S : Separation D Q hb a j x, S.Compatible (stateAfter D Q hb a N j word N x))

noncomputable def badFollowing (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) : Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x =>
    (stateAfter D Q hb a N j word N x).aborted = false ∧
    ∃ S : Separation D Q hb a j x, S.Compatible (stateAfter D Q hb a N j word N x))

theorem normalBad_conditional_bound (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l) (hD : KStrong D (selectionBudget a b l))
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (word : Fin w → Fin 3)
    (fixed : Fin m → Choice b l) :
    let N := exposureCap a b l
    let T := prefixTree D Q hb a N j word N
    prob (normalBad D Q hb a N j word ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤ normalError a b l := by
  dsimp only
  let N := exposureCap a b l
  let T := prefixTree D Q hb a N j word N
  let s := stateAfter D Q hb a N j word N fixed
  have hstate : ∀ x ∈ historyEvent T fixed, stateAfter D Q hb a N j word N x = s := by
    intro x hx
    exact history_determines_state D Q hb a N j word N fixed x (Finset.mem_filter.mp hx).2
  by_cases hn : Normal D Q N s
  · have hs : Supported D Q s := (run_supported_balanced D Q hb hdis a N j word N (initial n m) fixed
      (by simp [Supported,initial]) (by simp [Balanced,initial])).1
    have ht := normal_stopping_bound D Q hb hl j hD hdis hcover s hs hn.2.2 hn.2.1.le T fixed
      (stateAfter_seen D Q hb a N j word N fixed)
    apply le_trans _ ht
    apply div_le_div_of_nonneg_right _ (prob_nonneg _)
    apply prob_mono
    intro x hx
    obtain ⟨hE,hH⟩ := Finset.mem_inter.mp hx
    obtain ⟨_,S,hS⟩ := (Finset.mem_filter.mp hE).2
    refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,S,?_⟩,hH⟩
    rwa [hstate x hH] at hS
  · have hempty : normalBad D Q hb a N j word ∩ historyEvent T fixed = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      have hH := (Finset.mem_inter.mp hx).2
      have hN := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2.1
      rw [hstate x hH] at hN
      exact hn hN
    change prob (normalBad D Q hb a N j word ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤ _
    rw [hempty]
    simpa [prob] using normalError_nonneg a b l

theorem normalBad_bound (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l) (hD : KStrong D (selectionBudget a b l))
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (word : Fin w → Fin 3) :
    prob (normalBad D Q hb a (exposureCap a b l) j word) ≤ normalError a b l := by
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero l := ⟨hl.ne'⟩
  let N := exposureCap a b l
  let T := prefixTree D Q hb a N j word N
  apply average_conditional_bounds T.transcript _ _
  intro h hh
  obtain ⟨fixed,_,rfl⟩ := Finset.mem_image.mp hh
  exact normalBad_conditional_bound D Q hb hl j hD hdis hcover word fixed

theorem badFollowing_subset (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) :
    badFollowing D Q hb a N j word ⊆ overflow D Q hb a N j word ∪ normalBad D Q hb a N j word := by
  intro x hx
  obtain ⟨hn,S,hS⟩ := (Finset.mem_filter.mp hx).2
  rcases final_stop_cases D Q hb a N j word x with ha | hcap | hnormal
  · rw [hn] at ha; contradiction
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcap⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnormal,S,hS⟩)

theorem one_record_bad_bound (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (ha : 2 ≤ a) (hthree : ¬3 ∣ b) (j : Fin l)
    (hD : KStrong D (selectionBudget a b l)) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (word : Fin w → Fin 3) :
    prob (badFollowing D Q hb a (exposureCap a b l) j word) ≤ 3*Real.exp (-128*(a : ℝ)) := by
  have hO := overflow_selection_budget D Q hb hl hthree hdis a (by omega) hα j word
  have hN := normalBad_bound D Q hb hl j hD hdis hcover word
  have hU := (prob_mono (badFollowing_subset D Q hb a (exposureCap a b l) j word)).trans (prob_union_le _ _)
  have ht : prob (badFollowing D Q hb a (exposureCap a b l) j word) ≤
      Real.exp (-256*(a : ℝ)*l)+normalError a b l := by
    exact hU.trans (add_le_add hO hN)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have he : -256*(a : ℝ)*l = -(selectionK a b l/(256*b^2*l)) := by
    dsimp [selectionK]; field_simp; ring
  rw [he] at ht
  have htail := one_record_tail (a : ℝ) b l (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hl)
  rw [record_exponent a b l hbR hlR] at htail
  have hcombine : Real.exp (-(selectionK a b l/(256*b^2*l)))+normalError a b l ≤ 3*Real.exp (-128*(a : ℝ)) := by
    simpa only [normalError,neg_div,neg_mul,add_assoc] using htail
  exact ht.trans hcombine

noncomputable def separationEvent (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (a : Nat) (j : Fin l) : Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x => Nonempty (Separation D Q hb a j x))

theorem separation_probability_bound (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (ha : 2 ≤ a) (hthree : ¬3 ∣ b) (j : Fin l)
    (hD : KStrong D (selectionBudget a b l)) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) :
    prob (separationEvent D Q hb a j) ≤ 3*(9 : ℝ)^a*Real.exp (-128*(a : ℝ)) := by
  let records := (Finset.univ : Finset (Fin (2*a-1) → Fin 3))
  let E := fun word : Fin (2*a-1) → Fin 3 => badFollowing D Q hb a (exposureCap a b l) j word
  have hsub : separationEvent D Q hb a j ⊆ records.biUnion E := by
    intro x hx
    obtain ⟨S⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨word,hn,hS⟩ := S.exists_compatible_record (by omega) hα hdis (exposureCap a b l)
    exact Finset.mem_biUnion.mpr ⟨word,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn,S,hS⟩⟩
  have hcard : (records.card : ℝ) ≤ (9 : ℝ)^a := by
    have hh := (record_count a (by omega)).le
    simpa only [records,Finset.card_univ,Nat.cast_pow,Nat.cast_ofNat] using
      (show (Fintype.card (Fin (2*a-1) → Fin 3) : ℝ) ≤ ((9^a : Nat) : ℝ) by exact_mod_cast hh)
  calc
    _ ≤ prob (records.biUnion E) := prob_mono hsub
    _ ≤ ∑ word ∈ records, prob (E word) := prob_biUnion_le records E
    _ ≤ ∑ _word ∈ records, 3*Real.exp (-128*(a : ℝ)) := by
      apply Finset.sum_le_sum
      intro word _
      exact one_record_bad_bound D Q hb hl ha hthree j hD hα hdis hcover word
    _ = (records.card : ℝ)*(3*Real.exp (-128*(a : ℝ))) := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 3*Real.exp (-128*(a : ℝ)))]

theorem all_separations_probability (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (ha : 2 ≤ a) (hthree : ¬3 ∣ b)
    (hlmax : l ≤ 2*a) (hD : KStrong D (selectionBudget a b l)) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) :
    prob (Finset.univ.biUnion (fun j : Fin l => separationEvent D Q hb a j)) < (1 : ℝ)/16 := by
  have hsum := prob_biUnion_le Finset.univ (fun j : Fin l => separationEvent D Q hb a j)
  have hbnd : (∑ j : Fin l, prob (separationEvent D Q hb a j)) ≤
      3*(l : ℝ)*(9 : ℝ)^a*Real.exp (-128*(a : ℝ)) := by
    calc
      _ ≤ ∑ _j : Fin l, 3*(9 : ℝ)^a*Real.exp (-128*(a : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact separation_probability_bound D Q hb hl ha hthree j hD hα hdis hcover
      _ = _ := by simp; ring
  exact (hsum.trans hbnd).trans_lt (all_records_tail a l ha (by exact_mod_cast hlmax))

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.normalBad_bound
#print axioms ChvatalErdos.Record.one_record_bad_bound
#print axioms ChvatalErdos.Record.all_separations_probability
