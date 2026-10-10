import ChvatalErdos.AncestorBranch
import Mathlib.Data.Finset.Max

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.RootedParent
variable {n : Nat} {D : Digraph (Fin n)} {U : Finset (Fin n)} (T : RootedParent D U)

theorem split_level (Y : Finset (Fin n)) (hYU : Y ⊆ U) (i : Nat)
    (hlevel : ∀ v ∈ Y, T.depth v = i) (hmany : 1 < Y.card) :
    ∃ q A, q < i ∧ A ⊆ Y ∧ A.Nonempty ∧ (Y \ A).Nonempty ∧
      ∀ a ∈ A, ∀ b ∈ Y \ A, ∃ P : UPath D,
        P.first = a ∧ P.last = b ∧ P.vertices.length = 2*(i-q)+1 ∧
        P.support ⊆ U ∧ ∀ z ∈ P.support, T.depth z < i ∨ z = a ∨ z = b := by
  obtain ⟨a₀,ha₀⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
  let S := (Finset.range (i+1)).filter (fun j => ∀ v ∈ Y, T.ancestor v j = T.ancestor a₀ j)
  have hz : 0 ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega),?_⟩
    intro v hv
    rw [T.ancestor_zero v (hYU hv),T.ancestor_zero a₀ (hYU ha₀)]
  let q := S.max' ⟨0,hz⟩
  have hqS : q ∈ S := S.max'_mem _
  have hqle : q ≤ i := by have hh := Finset.mem_range.mp (Finset.mem_filter.mp hqS).1; omega
  have hcommon : ∀ v ∈ Y, T.ancestor v q = T.ancestor a₀ q := (Finset.mem_filter.mp hqS).2
  have hq : q < i := by
    by_contra h
    have hqi : q = i := by omega
    have hsub : Y ⊆ {a₀} := by
      intro v hv
      apply Finset.mem_singleton.mpr
      have he := hcommon v hv
      rw [hqi,← hlevel v hv,T.ancestor_self] at he
      rw [hlevel v hv,← hlevel a₀ ha₀,T.ancestor_self] at he
      exact he
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega
  have hnext : ∃ b ∈ Y, T.ancestor b (q+1) ≠ T.ancestor a₀ (q+1) := by
    by_contra h
    push_neg at h
    have hmem : q+1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),h⟩
    have hh : q+1 ≤ q := S.le_max' _ hmem
    omega
  let A := Y.filter (fun v => T.ancestor v (q+1) = T.ancestor a₀ (q+1))
  have hAY : A ⊆ Y := Finset.filter_subset _ _
  have hA : a₀ ∈ A := Finset.mem_filter.mpr ⟨ha₀,rfl⟩
  obtain ⟨b₀,hb₀,hb₀ne⟩ := hnext
  have hbA : b₀ ∈ Y \ A := by simp only [A,Finset.mem_sdiff,Finset.mem_filter]; exact ⟨hb₀,fun h => hb₀ne h.2⟩
  refine ⟨q,A,hq,hAY,⟨a₀,hA⟩,⟨b₀,hbA⟩,?_⟩
  intro a ha b hb
  have haY := hAY ha
  have hbY := (Finset.mem_sdiff.mp hb).1
  apply T.branch_path a b (hYU haY) (hYU hbY) i q (hlevel a haY) (hlevel b hbY) hq
  · rw [hcommon a haY,hcommon b hbY]
  · intro he
    have haeq := (Finset.mem_filter.mp ha).2
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨hbY,he.symm.trans haeq⟩)

end ChvatalErdos.RootedParent

#print axioms ChvatalErdos.RootedParent.split_level
