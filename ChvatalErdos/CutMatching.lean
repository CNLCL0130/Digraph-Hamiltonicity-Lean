import ChvatalErdos.Core
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ChvatalErdos

theorem partial_hall {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (t : A → Finset B) (k : Nat) (hk : k ≤ Fintype.card A)
    (hdef : ∀ s : Finset A, s.card ≤ (s.biUnion t).card + (Fintype.card A - k)) :
    ∃ s : Finset A, k ≤ s.card ∧ ∃ f : s → B, Function.Injective f ∧ ∀ a : s, f a ∈ t a := by
  classical
  let d := Fintype.card A - k
  let t' : A → Finset (B ⊕ Fin d) := fun a => (t a).disjSum Finset.univ
  have hhall : ∀ s : Finset A, s.card ≤ (s.biUnion t').card := by
    intro s
    by_cases hs : s.Nonempty
    · have heq : s.biUnion t' = (s.biUnion t).disjSum Finset.univ := by
        ext x
        cases x with
        | inl b => simp [t']
        | inr i => simpa [t'] using hs
      rw [heq, Finset.card_disjSum]
      simpa [d] using hdef s
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t').mp hhall
  let s : Finset A := Finset.univ.filter (fun a => ∃ b, f a = Sum.inl b)
  have hs : ∀ a : s, ∃ b, f a = Sum.inl b := fun a => (Finset.mem_filter.mp a.property).2
  let g : s → B := fun a => Classical.choose (hs a)
  have hg : ∀ a : s, f a = Sum.inl (g a) := fun a => Classical.choose_spec (hs a)
  have hgi : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hf
    rw [hg a, hg b, hab]
  have hgt : ∀ a : s, g a ∈ t a := by
    intro a
    have h := hft a
    rw [hg a] at h
    simpa [t'] using h
  have hright : ∀ a : (Finset.univ \ s : Finset A), ∃ i : Fin d, f a = Sum.inr i := by
    intro a
    have ha : a.val ∉ s := (Finset.mem_sdiff.mp a.property).2
    cases hfa : f a with
    | inl b => exact (ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hfa⟩)).elim
    | inr i => exact ⟨i, rfl⟩
  let j : (Finset.univ \ s : Finset A) → Fin d := fun a => Classical.choose (hright a)
  have hj : ∀ a : (Finset.univ \ s : Finset A), f a = Sum.inr (j a) :=
    fun a => Classical.choose_spec (hright a)
  have hji : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply hf
    rw [hj a, hj b, hab]
  have hcard := Fintype.card_le_of_injective j hji
  have hcard' : (Finset.univ \ s : Finset A).card ≤ d := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
  have htotal : (Finset.univ \ s : Finset A).card = Fintype.card A - s.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have hsle : s.card ≤ Fintype.card A := Finset.card_le_univ _
  refine ⟨s, ?_, g, hgi, hgt⟩
  dsimp [d] at hcard'
  omega

noncomputable def cutNeighbours {n : Nat} (D : Digraph (Fin n)) (A : Finset (Fin n))
    (u : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => v ∉ A ∧ D.arc u v)

theorem cut_neighbour_deficiency {n K k : Nat} (D : Digraph (Fin n)) (hstrong : KStrong D K)
    (A : Finset (Fin n)) (hk : k ≤ K) (hA : k ≤ A.card)
    (hB : k ≤ (Finset.univ \ A : Finset (Fin n)).card)
    (s : Finset (Fin n)) (hsA : s ⊆ A) :
    s.card ≤ (s.biUnion (cutNeighbours D A)).card + (A.card - k) := by
  classical
  by_contra hfail
  let N := s.biUnion (cutNeighbours D A)
  let C := (A \ s) ∪ N
  have hsle : s.card ≤ A.card := Finset.card_le_card hsA
  have hNsmall : N.card < k := by dsimp [N]; omega
  have hCsize : C.card < K := by
    have hcu := Finset.card_union_le (A \ s) N
    rw [Finset.card_sdiff_of_subset hsA] at hcu
    dsimp [C]
    have hfail' : N.card + (A.card - k) < s.card := Nat.lt_of_not_ge hfail
    omega
  have hNoutside : ∀ v ∈ N, v ∉ A := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp huv).2.1
  have hsnon : s.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, hu⟩ := hsnon
  obtain ⟨v, hvB, hvN⟩ := Finset.exists_mem_notMem_of_card_lt_card (hNsmall.trans_le hB)
  have huC : u ∉ C := by
    intro huC
    rcases Finset.mem_union.mp huC with h | h
    · exact (Finset.mem_sdiff.mp h).2 hu
    · exact hNoutside u h (hsA hu)
  have hvC : v ∉ C := by
    intro hvC
    rcases Finset.mem_union.mp hvC with h | h
    · exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_sdiff.mp h).1
    · exact hvN h
  obtain ⟨x,y,hx,hy,hxy⟩ := kStrong_cut_has_arc D hstrong C.toList (Finset.nodup_toList _)
    (by simpa using hCsize) (fun x => x ∈ s) (fun y => y ∉ A ∧ y ∉ N)
    (by
      intro z hz
      have hzC : z ∉ C := by simpa using hz
      by_cases hzs : z ∈ s
      · exact Or.inl hzs
      · apply Or.inr
        constructor
        · intro hzA
          exact hzC (Finset.mem_union_left N (Finset.mem_sdiff.mpr ⟨hzA,hzs⟩))
        · intro hzN
          exact hzC (Finset.mem_union_right (A \ s) hzN))
    (fun z hzs hz => hz.1 (hsA hzs))
    ⟨u, by simpa using huC, hu⟩
    ⟨v, by simpa using hvC, (Finset.mem_sdiff.mp hvB).2, hvN⟩
  apply hy.2
  exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy.1,hxy⟩⟩

/-- A matching across an oriented cut, derived directly from finite Hall and vertex connectivity. -/
theorem cut_matching {n K k : Nat} (D : Digraph (Fin n)) (hstrong : KStrong D K)
    (A : Finset (Fin n)) (hk : k ≤ K) (hA : k ≤ A.card)
    (hB : k ≤ (Finset.univ \ A : Finset (Fin n)).card) :
    ∃ s : Finset A, k ≤ s.card ∧ ∃ f : s → Fin n, Function.Injective f ∧
      ∀ u : s, f u ∉ A ∧ D.arc u.val.val (f u) := by
  classical
  have hdef : ∀ s : Finset A, s.card ≤ (s.biUnion (fun u => cutNeighbours D A u)).card +
      (Fintype.card A - k) := by
    intro s
    let S := s.image (fun u : A => u.val)
    have hsA : S ⊆ A := by
      intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      exact v.property
    have hcard : S.card = s.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hN : S.biUnion (cutNeighbours D A) = s.biUnion (fun u => cutNeighbours D A u) := by
      ext v
      simp [S]
    have h := cut_neighbour_deficiency D hstrong A hk hA hB S hsA
    rw [hcard,hN] at h
    simpa only [Fintype.card_coe] using h
  obtain ⟨s,hsize,f,hfi,hf⟩ := partial_hall (fun u : A => cutNeighbours D A u) k
    (by simpa only [Fintype.card_coe] using hA) hdef
  refine ⟨s,hsize,f,hfi,?_⟩
  intro u
  exact (Finset.mem_filter.mp (hf u)).2

end ChvatalErdos

#print axioms ChvatalErdos.partial_hall
#print axioms ChvatalErdos.cut_neighbour_deficiency
#print axioms ChvatalErdos.cut_matching
