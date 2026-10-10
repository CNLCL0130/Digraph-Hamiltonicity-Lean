import ChvatalErdos.PackingCoordinates
import ChvatalErdos.NeighbourObstruction
import ChvatalErdos.WeightedFailure

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints FiniteProbability Record
variable {n m b l a K : Nat}

theorem all_coordinate_count (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (P : Fin n → Prop) :
    (∑ i : Fin m, ((Finset.univ.filter (fun t => P ((Q i).vertex t))).card : ℝ)) =
      ((Finset.univ.filter P).card : ℝ) := by
  have hU : verticesOf D Q Finset.univ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    obtain ⟨i,t,rfl⟩ := hcover z
    exact vertex_in_verticesOf D Q Finset.univ i (Finset.mem_univ _) t
  have he := coordinate_count D Q hdis Finset.univ P
  rw [hU] at he
  simp only [Finset.mem_univ,if_true] at he
  exact_mod_cast he

noncomputable def directedNeighbours (D : Digraph (Fin n)) (outgoing : Bool) (z : Fin n) : Finset (Fin n) :=
  if outgoing then outNeighbours D z else inNeighbours D z

noncomputable def vertexChoices (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (outgoing : Bool) (z : Fin n) (i : Fin m) : Finset (Fin b) :=
  Finset.univ.filter (fun t => if outgoing then D.arc z ((Q i).vertex t) else D.arc ((Q i).vertex t) z)

noncomputable def vertexNeighbourFailure (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (outgoing : Bool) (own : Fin n → Fin m) (j : Fin l) (threshold : ℝ) (z : Fin n) :
    Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x => successCount (fun i => directedNeighbourEvent hb outgoing
    (if i = own z then ∅ else vertexChoices D Q outgoing z i) j) x < threshold)

theorem vertex_neighbour_failure_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (hD : KStrong D K)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (outgoing : Bool) (own : Fin n → Fin m) (j : Fin l) (hK : 2*b ≤ K) (z : Fin n) :
    prob (vertexNeighbourFailure D Q hb outgoing own j ((K : ℝ)/(4*b*l)) z) ≤
      Real.exp (-((directedNeighbours D outgoing z).card : ℝ)/(16*b*l)) := by
  have hcount : (∑ i, ((vertexChoices D Q outgoing z i).card : ℝ)) = ((directedNeighbours D outgoing z).card : ℝ) := by
    cases outgoing
    · exact all_coordinate_count D Q hdis hcover (fun v => D.arc v z)
    · exact all_coordinate_count D Q hdis hcover (fun v => D.arc z v)
  have hd : (K : ℝ) ≤ ((directedNeighbours D outgoing z).card : ℝ) := by
    cases outgoing
    · exact_mod_cast kStrong_indegree D hD z
    · exact_mod_cast kStrong_outdegree D hD z
  have hm := count_excluding_one_cycle (vertexChoices D Q outgoing z) (own z)
  rw [hcount] at hm
  have ht : prob (Finset.univ.filter (fun x : Fin m → Choice b l =>
      successCount (fun i => directedNeighbourEvent hb outgoing
        (if i = own z then ∅ else vertexChoices D Q outgoing z i) j) x ≤ (K : ℝ)/(4*b*l))) ≤
      Real.exp (-((directedNeighbours D outgoing z).card : ℝ)/(16*b*l)) := by
    cases outgoing
    · exact exit_neighbour_tail hb hl _ j _ K (by exact_mod_cast hK) hd hm
    · exact neighbour_tail (by omega) hl _ j _ K (by exact_mod_cast hK) hd hm
  apply le_trans _ ht
  apply prob_mono
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hx).2).le⟩

theorem vertex_neighbour_union (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (hD : KStrong D K) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (outgoing : Bool) (own : Fin n → Fin m) (j : Fin l)
    (hK : 2*b ≤ K) (hscale : 16*b*l ≤ K+1) :
    prob (Finset.univ.biUnion (vertexNeighbourFailure D Q hb outgoing own j ((K : ℝ)/(4*b*l)))) ≤
      (a : ℝ)*(K+1)*Real.exp (-(K : ℝ)/(16*b*l)) := by
  apply degree_weighted_union_bound D a hα _ (fun z => ((directedNeighbours D outgoing z).card : ℝ))
    K (16*b*l) (Nat.cast_nonneg _) (by positivity) (by exact_mod_cast hscale)
  · intro z
    cases outgoing
    · exact_mod_cast kStrong_indegree D hD z
    · exact_mod_cast kStrong_outdegree D hD z
  · intro z
    have hh : twoCycleDegree D z ≤ (directedNeighbours D outgoing z).card := by
      apply Finset.card_le_card
      intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      cases outgoing
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'.2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'.1⟩
    exact_mod_cast hh
  · intro z
    exact vertex_neighbour_failure_tail D Q hb hl hD hdis hcover outgoing own j hK z

noncomputable def terminalCoordinates (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (B : Finset (Fin n)) (i : Fin m) : Finset (Fin b) :=
  Finset.univ.filter (fun t => (Q i).vertex t ∈ B)

noncomputable def terminalNeighbourFailure (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (outgoing : Bool) (B : Finset (Fin n)) (j : Fin l) (threshold : ℝ) :
    Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x => successCount (fun i => directedNeighbourEvent hb outgoing
    (terminalCoordinates D Q B i) j) x < threshold)

theorem terminal_neighbour_failure_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (outgoing : Bool) (B : Finset (Fin n)) (j : Fin l) (hK : 2*b ≤ K) (hB : K ≤ B.card) :
    prob (terminalNeighbourFailure D Q hb outgoing B j ((K : ℝ)/(4*b*l))) ≤
      Real.exp (-(K : ℝ)/(16*b*l)) := by
  have hcount : (∑ i, ((terminalCoordinates D Q B i).card : ℝ)) = (B.card : ℝ) := by
    have h0 := all_coordinate_count D Q hdis hcover (fun v => v ∈ B)
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    congr 1
    ext t
    simp [terminalCoordinates]
  have hm : (B.card : ℝ)-b ≤ ∑ i, ((terminalCoordinates D Q B i).card : ℝ) := by rw [hcount]; linarith [Nat.cast_nonneg (α := ℝ) b]
  have ht : prob (Finset.univ.filter (fun x : Fin m → Choice b l =>
      successCount (fun i => directedNeighbourEvent hb outgoing (terminalCoordinates D Q B i) j) x ≤ (K : ℝ)/(4*b*l))) ≤
      Real.exp (-(B.card : ℝ)/(16*b*l)) := by
    cases outgoing
    · exact exit_neighbour_tail hb hl _ j B.card K (by exact_mod_cast hK) (by exact_mod_cast hB) hm
    · exact neighbour_tail (by omega) hl _ j B.card K (by exact_mod_cast hK) (by exact_mod_cast hB) hm
  have hsub : terminalNeighbourFailure D Q hb outgoing B j ((K : ℝ)/(4*b*l)) ⊆
      Finset.univ.filter (fun x : Fin m → Choice b l =>
        successCount (fun i => directedNeighbourEvent hb outgoing (terminalCoordinates D Q B i) j) x ≤ (K : ℝ)/(4*b*l)) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hx).2).le⟩
  apply ((prob_mono hsub).trans ht).trans
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right
  · exact neg_le_neg (by exact_mod_cast hB)
  · positivity

noncomputable def allNeighbourFailures {t : Nat} (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (own : Fin n → Fin m) (B : Bool → Fin t → Finset (Fin n)) (threshold : ℝ) :
    Finset (Fin m → Choice b l) :=
  Finset.univ.biUnion (fun p : Bool × Fin l =>
    Finset.univ.biUnion (vertexNeighbourFailure D Q hb p.1 own p.2 threshold) ∪
      Finset.univ.biUnion (fun z : Fin t => terminalNeighbourFailure D Q hb p.1 (B p.1 z) p.2 threshold))

theorem all_neighbour_failure_bound {t : Nat} (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (hD : KStrong D K) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (own : Fin n → Fin m) (B : Bool → Fin t → Finset (Fin n)) (hT : t ≤ 2*a)
    (hB : ∀ outgoing z, K ≤ (B outgoing z).card) (hK : 2*b ≤ K) (hscale : 16*b*l ≤ K+1) :
    prob (allNeighbourFailures (l := l) D Q hb own B ((K : ℝ)/(4*b*l))) ≤
      2*(a : ℝ)*l*(K+3)*Real.exp (-(K : ℝ)/(16*b*l)) := by
  let eps := Real.exp (-(K : ℝ)/(16*b*l))
  let E := fun p : Bool × Fin l =>
    Finset.univ.biUnion (vertexNeighbourFailure D Q hb p.1 own p.2 ((K : ℝ)/(4*b*l))) ∪
      Finset.univ.biUnion (fun z : Fin t => terminalNeighbourFailure D Q hb p.1 (B p.1 z) p.2 ((K : ℝ)/(4*b*l)))
  have hpair : ∀ p, prob (E p) ≤ (a : ℝ)*(K+3)*eps := by
    intro p
    have hv := vertex_neighbour_union D Q hb hl hD hα hdis hcover p.1 own p.2 hK hscale
    have ht : prob (Finset.univ.biUnion (fun z : Fin t => terminalNeighbourFailure D Q hb p.1 (B p.1 z) p.2 ((K : ℝ)/(4*b*l)))) ≤
        (t : ℝ)*eps := by
      apply (prob_biUnion_le Finset.univ _).trans
      calc
        _ ≤ ∑ _z : Fin t, eps := by
          apply Finset.sum_le_sum
          intro z _
          exact terminal_neighbour_failure_tail D Q hb hl hdis hcover p.1 (B p.1 z) p.2 hK (hB p.1 z)
        _ = _ := by simp
    have hu := prob_union_le
      (Finset.univ.biUnion (vertexNeighbourFailure D Q hb p.1 own p.2 ((K : ℝ)/(4*b*l))))
      (Finset.univ.biUnion (fun z : Fin t => terminalNeighbourFailure D Q hb p.1 (B p.1 z) p.2 ((K : ℝ)/(4*b*l))))
    apply (hu.trans (add_le_add hv ht)).trans
    have hTR : (t : ℝ) ≤ 2*(a : ℝ) := by exact_mod_cast hT
    have hh := mul_le_mul_of_nonneg_right hTR (Real.exp_pos (-(K : ℝ)/(16*b*l))).le
    change (a : ℝ)*(K+1)*eps + (t : ℝ)*eps ≤ (a : ℝ)*(K+3)*eps
    nlinarith
  apply (prob_biUnion_le Finset.univ E).trans
  calc
    _ ≤ ∑ _p : Bool × Fin l, (a : ℝ)*(K+3)*eps := Finset.sum_le_sum (fun p _ => hpair p)
    _ = _ := by simp [Fintype.card_prod,eps]; ring

end ChvatalErdos

#print axioms ChvatalErdos.vertex_neighbour_union
#print axioms ChvatalErdos.all_neighbour_failure_bound
