import ChvatalErdos.CutMatching
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace ChvatalErdos

/-- The matching reduction for set linkage. Markers stand for a source on the
left and a sink on the right. Internal vertices may be matched to themselves. -/
def LinkRel {n r : Nat} (D : Digraph (Fin n))
    (out inn : Fin r → Finset (Fin n)) : (Fin n ⊕ Fin r) → (Fin n ⊕ Fin r) → Prop
  | .inl u, .inl v => u = v ∨ D.arc u v
  | .inl u, .inr j => u ∈ inn j
  | .inr i, .inl v => v ∈ out i
  | .inr _, .inr _ => False

theorem linkage_permutation {n r h : Nat} (D : Digraph (Fin n))
    (hD : KStrong D h) (hr : r ≤ h) (out inn : Fin r → Finset (Fin n))
    (hout : ∀ i, h ≤ (out i).card) (hinn : ∀ i, h ≤ (inn i).card) :
    ∃ f : Equiv.Perm (Fin n ⊕ Fin r), ∀ v, LinkRel D out inn v (f v) := by
  classical
  let t : (Fin n ⊕ Fin r) → Finset (Fin n ⊕ Fin r) :=
    fun v => Finset.univ.filter (LinkRel D out inn v)
  have ht : ∀ v w, w ∈ t v ↔ LinkRel D out inn v w := by simp [t]
  have hhall : ∀ s : Finset (Fin n ⊕ Fin r), s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra hfail
    let N := s.biUnion t
    let A := s.toLeft
    let I := s.toRight
    let B := N.toLeft
    let Y := N.toRight
    let S := B \ A
    have hAB : A ⊆ B := by
      intro v hv
      apply Finset.mem_toLeft.mpr
      exact Finset.mem_biUnion.mpr ⟨.inl v,Finset.mem_toLeft.mp hv,
        (ht _ _).2 (Or.inl rfl)⟩
    have hsmall : S.card + Y.card < I.card := by
      have hs := s.card_toLeft_add_card_toRight
      have hn := N.card_toLeft_add_card_toRight
      have hab := Finset.card_le_card hAB
      have hsc : S.card = B.card - A.card := Finset.card_sdiff_of_subset hAB
      change ¬ s.card ≤ N.card at hfail
      dsimp [A,I,B,Y] at hsc hab ⊢
      omega
    have hI : I.card ≤ r := by simpa [I] using Finset.card_le_univ I
    have hS : S.card < h := by omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
    have hnotOut : ¬ out i ⊆ S := by
      intro hsub
      have hc := Finset.card_le_card hsub
      have := hout i
      omega
    obtain ⟨u,hu,hunS⟩ := Finset.not_subset.mp hnotOut
    have huB : u ∈ B := by
      apply Finset.mem_toLeft.mpr
      exact Finset.mem_biUnion.mpr ⟨.inr i,Finset.mem_toRight.mp hi,(ht _ _).2 hu⟩
    have huA : u ∈ A := by
      by_contra hn
      exact hunS (Finset.mem_sdiff.mpr ⟨huB,hn⟩)
    have hnotY : ¬ (Finset.univ : Finset (Fin r)) ⊆ Y := by
      intro hsub
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_univ,Fintype.card_fin] at hc
      omega
    obtain ⟨j,_,hj⟩ := Finset.not_subset.mp hnotY
    have hnotIn : ¬ inn j ⊆ S := by
      intro hsub
      have hc := Finset.card_le_card hsub
      have := hinn j
      omega
    obtain ⟨v,hv,hvnS⟩ := Finset.not_subset.mp hnotIn
    have hvnA : v ∉ A := by
      intro hvA
      apply hj
      apply Finset.mem_toRight.mpr
      exact Finset.mem_biUnion.mpr ⟨.inl v,Finset.mem_toLeft.mp hvA,(ht _ _).2 hv⟩
    have hstrong := hD.2 S.toList (Finset.nodup_toList _) (by simpa using hS)
    have hreach := hstrong.2 u v (by simpa using hunS) (by simpa using hvnS)
    have hstay : u ∈ A → ∀ w, Reach D (fun z => z ∉ S.toList) u w → w ∈ A := by
      intro huA w hw
      induction hw with
      | refl _ => exact huA
      | @step z w _ he hw ih =>
        have hwB : w ∈ B := by
          apply Finset.mem_toLeft.mpr
          exact Finset.mem_biUnion.mpr ⟨.inl z,Finset.mem_toLeft.mp ih,
            (ht _ _).2 (Or.inr he)⟩
        have hwnS : w ∉ S := by simpa using hw
        by_contra hn
        exact hwnS (Finset.mem_sdiff.mpr ⟨hwB,hn⟩)
    exact hvnA (hstay huA v hreach)
  obtain ⟨f,hf,hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩,?_⟩
  intro v
  exact (ht v (f v)).1 (hft v)

end ChvatalErdos

#print axioms ChvatalErdos.linkage_permutation

