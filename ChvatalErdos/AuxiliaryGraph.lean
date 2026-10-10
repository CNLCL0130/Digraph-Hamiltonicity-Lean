import ChvatalErdos.RecordSeparations
import ChvatalErdos.Connectivity

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints
variable {n m b l a : Nat}

def auxiliary (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (sample : Fin m → Choice b l) : Digraph (Fin m) where
  arc i k := i ≠ k ∧ D.arc ((Q i).vertex (exit hb (sample i))) ((Q k).vertex (entrance (sample k)))
  loopless _ h := h.1 rfl

noncomputable def active (sample : Fin m → Choice b l) (j : Fin l) : Finset (Fin m) :=
  Finset.univ.filter (fun i => colour (sample i) = j)

theorem auxiliary_arc_expands (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (sample : Fin m → Choice b l) (i k : Fin m) (h : (auxiliary D Q hb sample).arc i k) :
    D.arc ((Q i).selectedPath hb (sample i)).last ((Q k).selectedPath hb (sample k)).first := by
  rw [((Q i).selected_endpoints hb (sample i)).2,((Q k).selected_endpoints hb (sample k)).1]
  exact h.2

/-- A failure of reachability after a small deletion yields a separation in
the exact index representation used by the record algorithm. -/
theorem separation_of_nonreach (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (sample : Fin m → Choice b l) (j : Fin l) (T : Finset (Fin m)) (hT : T.card < a)
    (u v : Fin m) (hu : u ∈ active sample j ∧ u ∉ T) (hv : v ∈ active sample j ∧ v ∉ T)
    (hn : ¬Reach (auxiliary D Q hb sample) (fun i => i ∈ active sample j ∧ i ∉ T) u v) :
    Nonempty (Record.Separation D Q hb a j sample) := by
  let allowed := fun i => i ∈ active sample j ∧ i ∉ T
  let reaches := fun i => Reach (auxiliary D Q hb sample) allowed u i
  let L := Finset.univ.filter (fun i => allowed i ∧ reaches i)
  let R := Finset.univ.filter (fun i => allowed i ∧ ¬reaches i)
  let X := active sample j ∩ T
  have hL : ∀ i, i ∈ L ↔ allowed i ∧ reaches i := by simp [L]
  have hR : ∀ i, i ∈ R ↔ allowed i ∧ ¬reaches i := by simp [R]
  have hX : ∀ i, i ∈ X ↔ i ∈ active sample j ∧ i ∈ T := by simp [X]
  refine ⟨{
    L := L
    X := X
    R := R
    left_nonempty := ⟨u,(hL u).2 ⟨hu,Reach.refl hu⟩⟩
    right_nonempty := ⟨v,(hR v).2 ⟨hv,hn⟩⟩
    left_separator := ?_
    left_right := ?_
    separator_right := ?_
    partition := ?_
    small := ?_
    no_arc := ?_ }⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact ((hL i).1 hi).1.2 ((hX i).1 hi').2
  · apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact ((hR i).1 hi').2 ((hL i).1 hi).2
  · apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact ((hR i).1 hi').1.2 ((hX i).1 hi).2
  · intro i
    have hc : colour (sample i) = j ↔ i ∈ active sample j := by simp [active]
    rw [hc,hL,hX,hR]
    constructor
    · intro hi
      by_cases hiT : i ∈ T
      · exact Or.inr (Or.inl ⟨hi,hiT⟩)
      · by_cases hr : reaches i
        · exact Or.inl ⟨⟨hi,hiT⟩,hr⟩
        · exact Or.inr (Or.inr ⟨⟨hi,hiT⟩,hr⟩)
    · rintro (hi | hi | hi)
      · exact hi.1.1
      · exact hi.1
      · exact hi.1.1
  · exact lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_right) hT
  · intro i hi k hk he
    have hir := (hL i).1 hi
    have hkr := (hR k).1 hk
    have hik : i ≠ k := by
      intro heq
      exact hkr.2 (heq ▸ hir.2)
    exact hkr.2 (Reach.step hir.2 ⟨hik,he⟩ hkr.1)

theorem auxiliary_strong_of_no_separation (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (sample : Fin m → Choice b l) (j : Fin l)
    (hcard : a+1 ≤ (active sample j).card)
    (hno : ¬Nonempty (Record.Separation D Q hb a j sample)) :
    KStrongOn (auxiliary D Q hb sample) (active sample j) a := by
  refine ⟨hcard,?_⟩
  intro T hT
  have hnot : ¬active sample j ⊆ T := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨u,hu,huT⟩ := Finset.not_subset.mp hnot
  refine ⟨⟨u,hu,huT⟩,?_⟩
  intro x y hx hy
  by_contra hn
  exact hno (separation_of_nonreach D Q hb sample j T hT x y hx hy hn)

end ChvatalErdos

#print axioms ChvatalErdos.auxiliary_strong_of_no_separation
