import ChvatalErdos.GlobalNeighbours
import ChvatalErdos.RecordProbability
import ChvatalErdos.AuxiliaryGraph

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints FiniteProbability Record
variable {n m b l a : Nat}

theorem selection_scales (hb : 4 ≤ b) (hl : 0 < l) (ha : 2 ≤ a) :
    2*b ≤ selectionBudget a b l ∧ 16*b*l ≤ selectionBudget a b l+1 ∧
      (a+1 : ℝ) ≤ (selectionBudget a b l : ℝ)/(4*b*l) := by
  have hf : 0 < 4096*b*a*l := by positivity
  have hscale : 16*b*l ≤ selectionBudget a b l := by
    calc
      _ ≤ (16*b*l)*(4096*b*a*l) := Nat.le_mul_of_pos_right _ hf
      _ = _ := by dsimp [selectionBudget]; ring
  have hbase : 2*b ≤ 16*b*l := by nlinarith
  refine ⟨hbase.trans hscale,by omega,?_⟩
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have he : (selectionBudget a b l : ℝ)/(4*b*l) = 16384*(b : ℝ)*a*l := by
    dsimp [selectionBudget]; push_cast; field_simp; ring
  rw [he]
  have hbl : (1 : ℝ) ≤ (b : ℝ)*l := by exact_mod_cast (show 1 ≤ b*l by nlinarith)
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hh := mul_le_mul_of_nonneg_right hbl (by positivity : (0 : ℝ) ≤ a)
  nlinarith

theorem successCount_le_active (hb : 4 ≤ b) (outgoing : Bool)
    (events : Fin m → Finset (Fin b)) (j : Fin l) (x : Fin m → Choice b l) :
    successCount (fun i => directedNeighbourEvent hb outgoing (events i) j) x ≤ ((active x j).card : ℝ) := by
  have hcount : (∑ i : Fin m, if i ∈ active x j then (1 : ℝ) else 0) = ((active x j).card : ℝ) := by simp
  rw [← hcount]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i ∈ directedNeighbourEvent hb outgoing (events i) j
  · have hc : colour (x i) = j := by
      cases outgoing <;> exact (Finset.mem_filter.mp hi).2.2
    simp [hi,active,hc]
  · simp only [hi,if_false]
    positivity

/-- The random selection lemma, with arbitrary fixed terminal neighbourhoods.
The owner map specifies which cycle is excluded for each graph vertex. -/
theorem selection_exists {t : Nat} (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (ha : 2 ≤ a) (hthree : ¬3 ∣ b) (hlmax : l ≤ 2*a)
    (hD : KStrong D (selectionBudget a b l)) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (own : Fin n → Fin m) (B : Bool → Fin t → Finset (Fin n)) (hT : t ≤ 2*a)
    (hB : ∀ outgoing z, selectionBudget a b l ≤ (B outgoing z).card) :
    ∃ x : Fin m → Choice b l,
      (∀ j, KStrongOn (auxiliary D Q hb x) (active x j) a) ∧
      (∀ outgoing j z, (a : ℝ) ≤ successCount (fun i => directedNeighbourEvent hb outgoing
        (if i = own z then ∅ else vertexChoices D Q outgoing z i) j) x) ∧
      (∀ outgoing j z, (a : ℝ) ≤ successCount (fun i => directedNeighbourEvent hb outgoing
        (terminalCoordinates D Q (B outgoing z) i) j) x) := by
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero l := ⟨hl.ne'⟩
  let threshold : ℝ := (selectionBudget a b l : ℝ)/(4*b*l)
  let badN := allNeighbourFailures (l := l) D Q hb own B threshold
  let badS := Finset.univ.biUnion (fun j : Fin l => separationEvent D Q hb a j)
  have hscales := selection_scales hb hl ha
  have hN : prob badN < (1 : ℝ)/16 := by
    have ht := all_neighbour_failure_bound D Q hb hl hD hα hdis hcover own B hT hB hscales.1 hscales.2.1
    rw [selectionBudget_real] at ht
    dsimp [badN,threshold]
    rw [selectionBudget_real]
    apply ht.trans_lt
    simpa only [neg_div] using neighbour_failure a b l (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hl)
  have hS : prob badS < (1 : ℝ)/16 := all_separations_probability D Q hb hl ha hthree hlmax hD hα hdis hcover
  have hex : ∃ x : Fin m → Choice b l, x ∉ badN ∪ badS := by
    by_contra hno
    have heq : badN ∪ badS = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      by_contra hx
      exact hno ⟨x,hx⟩
    have hu := prob_union_le badN badS
    rw [heq,prob_univ] at hu
    linarith
  obtain ⟨x,hx⟩ := hex
  have hxN : x ∉ badN := fun h => hx (Finset.mem_union_left _ h)
  have hxS : x ∉ badS := fun h => hx (Finset.mem_union_right _ h)
  have hvertex : ∀ outgoing j z, threshold ≤ successCount (fun i => directedNeighbourEvent hb outgoing
      (if i = own z then ∅ else vertexChoices D Q outgoing z i) j) x := by
    intro outgoing j z
    apply le_of_not_gt
    intro hbad
    apply hxN
    exact Finset.mem_biUnion.mpr ⟨(outgoing,j),Finset.mem_univ _,Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩⟩)⟩
  have hterminal : ∀ outgoing j z, threshold ≤ successCount (fun i => directedNeighbourEvent hb outgoing
      (terminalCoordinates D Q (B outgoing z) i) j) x := by
    intro outgoing j z
    apply le_of_not_gt
    intro hbad
    apply hxN
    exact Finset.mem_biUnion.mpr ⟨(outgoing,j),Finset.mem_univ _,Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩⟩)⟩
  have hathreshold : (a : ℝ) ≤ threshold := by have hh := hscales.2.2; dsimp [threshold]; linarith
  refine ⟨x,?_,fun outgoing j z => hathreshold.trans (hvertex outgoing j z),
    fun outgoing j z => hathreshold.trans (hterminal outgoing j z)⟩
  intro j
  apply auxiliary_strong_of_no_separation D Q hb x j
  · have hn : 0 < n := by have hh := hD.1; omega
    let z : Fin n := ⟨0,hn⟩
    have hcount := successCount_le_active hb true
      (fun i => if i = own z then ∅ else vertexChoices D Q true z i) j x
    have hcard : (a+1 : ℝ) ≤ ((active x j).card : ℝ) := hscales.2.2.trans ((hvertex true j z).trans hcount)
    exact_mod_cast hcard
  · intro hsep
    apply hxS
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsep⟩⟩

theorem cycle_owners (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) :
    ∃ own : Fin n → Fin m, ∀ i t, own ((Q i).vertex t) = i := by
  choose own position hown using hcover
  refine ⟨own,?_⟩
  intro i t
  have he := coordinate_injective D Q hdis
    (a₁ := (own ((Q i).vertex t),position ((Q i).vertex t))) (a₂ := (i,t)) (hown ((Q i).vertex t))
  exact congrArg Prod.fst he

noncomputable def actualPathNeighbours (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (outgoing : Bool) (x : Fin m → Choice b l) (j : Fin l) (z : Fin n) : Finset (Fin m) :=
  (active x j).filter (fun i => z ∉ (Q i).support ∧
    if outgoing then D.arc z ((Q i).selectedPath hb (x i)).first else D.arc ((Q i).selectedPath hb (x i)).last z)

theorem actualPathNeighbours_count (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (own : Fin n → Fin m) (hown : ∀ i t, own ((Q i).vertex t) = i)
    (outgoing : Bool) (x : Fin m → Choice b l) (j : Fin l) (z : Fin n) :
    ((actualPathNeighbours D Q hb outgoing x j z).card : ℝ) =
      successCount (fun i => directedNeighbourEvent hb outgoing
        (if i = own z then ∅ else vertexChoices D Q outgoing z i) j) x := by
  have howner : ∀ i, i = own z ↔ z ∈ (Q i).support := by
    intro i
    constructor
    · intro hi
      obtain ⟨k,t,rfl⟩ := hcover z
      rw [hown] at hi
      subst i
      exact (Q k).mem_support _ |>.2 ⟨t,rfl⟩
    · intro hz
      obtain ⟨t,ht⟩ := (Q i).mem_support z |>.1 hz
      rw [← ht,hown]
  have hmem : ∀ i, i ∈ actualPathNeighbours D Q hb outgoing x j z ↔
      x i ∈ directedNeighbourEvent hb outgoing (if i = own z then ∅ else vertexChoices D Q outgoing z i) j := by
    intro i
    have hends := (Q i).selected_endpoints hb (x i)
    by_cases hi : i = own z
    · subst i
      have hzi := (howner (own z)).1 rfl
      cases outgoing <;> simp [actualPathNeighbours,active,directedNeighbourEvent,neighbourEvent,exitNeighbourEvent,hzi]
    · have hzi : z ∉ (Q i).support := fun hz => hi ((howner i).2 hz)
      cases outgoing <;> simp [actualPathNeighbours,active,directedNeighbourEvent,neighbourEvent,exitNeighbourEvent,
        vertexChoices,hi,hzi,hends.1,hends.2,and_comm]
  have hsum : (∑ i : Fin m, if i ∈ actualPathNeighbours D Q hb outgoing x j z then (1 : ℝ) else 0) =
      ((actualPathNeighbours D Q hb outgoing x j z).card : ℝ) := by simp
  rw [← hsum]
  simp only [successCount,hmem]

end ChvatalErdos

#print axioms ChvatalErdos.selection_exists
#print axioms ChvatalErdos.actualPathNeighbours_count
