import ChvatalErdos.CycleInsertion

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat} {D : Digraph (Fin n)} {I : Type} [Fintype I] [DecidableEq I]

/-- Unused resource paths may be inserted in either direction of their
retained edge. The chosen orientation follows the arc present in the cycle. -/
theorem hamiltonian_by_bidirectional_insertions (C : DCycle D) (used : Finset I)
    (R forward backward : I → DPath D) (u v : I → Fin n)
    (hforward : ∀ i, (forward i).support = (R i).support)
    (hbackward : ∀ i, (backward i).support = (R i).support)
    (hcovered : ∀ i ∈ used, (R i).support ⊆ C.path.support)
    (havoid : ∀ i, i ∉ used → Disjoint C.path.support (R i).support)
    (hdis : ∀ i j, i ≠ j → Disjoint (R i).support (R j).support)
    (harc : ∀ i, i ∉ used → C.HasArc (u i) (v i) ∨ C.HasArc (v i) (u i))
    (hends : ∀ i j, u i = u j ∨ u i = v j ∨ v i = u j ∨ v i = v j → i = j)
    (henterF : ∀ i, D.arc (u i) (forward i).first)
    (hleaveF : ∀ i, D.arc (forward i).last (v i))
    (henterB : ∀ i, D.arc (v i) (backward i).first)
    (hleaveB : ∀ i, D.arc (backward i).last (u i))
    (hspan : ∀ z, z ∈ C.path.support ∨ ∃ i, z ∈ (R i).support) : Hamiltonian D := by
  let unused := Finset.univ \ used
  let chooseForward := fun i => C.HasArc (u i) (v i)
  let Q := fun i => if chooseForward i then forward i else backward i
  let tail := fun i => if chooseForward i then u i else v i
  let head := fun i => if chooseForward i then v i else u i
  have hsupport : ∀ i, (Q i).support = (R i).support := by
    intro i
    dsimp [Q]
    split
    · exact hforward i
    · exact hbackward i
  apply hamiltonian_by_insertions C unused Q tail head
  · intro i hi
    have hni : i ∉ used := (Finset.mem_sdiff.mp hi).2
    dsimp [tail,head]
    split
    · assumption
    · exact (harc i hni).resolve_left (by assumption)
  · intro i hi
    rw [hsupport]
    exact havoid i (Finset.mem_sdiff.mp hi).2
  · intro i _ j _ hij
    rw [hsupport,hsupport]
    exact hdis i j hij
  · intro i _ j _ heq
    have ht := congrArg Prod.fst heq
    dsimp [tail] at ht
    apply hends i j
    split at ht <;> split at ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr (Or.inl ht))
    · exact Or.inr (Or.inr (Or.inr ht))
  · intro i _
    dsimp [tail,Q]
    split
    · exact henterF i
    · exact henterB i
  · intro i _
    dsimp [head,Q]
    split
    · exact hleaveF i
    · exact hleaveB i
  · intro z
    rcases hspan z with hz | ⟨i,hi⟩
    · exact Finset.mem_union_left _ hz
    · by_cases hu : i ∈ used
      · exact Finset.mem_union_left _ (hcovered i hu hi)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩,by rw [hsupport]; exact hi⟩)

end ChvatalErdos

#print axioms ChvatalErdos.hamiltonian_by_bidirectional_insertions
