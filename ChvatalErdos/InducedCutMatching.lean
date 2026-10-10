import ChvatalErdos.CutMatching
import ChvatalErdos.Connectivity

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n K k : Nat}

/-- A matching inside a vertex-induced strongly connected graph, with an
exact finite index type for the requested number of arcs. -/
theorem induced_cut_matching (D : Digraph (Fin n)) (U A B : Finset (Fin n))
    (hU : KStrongOn D U K) (hpartition : A ∪ B = U) (hdis : Disjoint A B)
    (hk : k ≤ K) (hA : k ≤ A.card) (hB : k ≤ B.card) :
    ∃ u v : Fin k → Fin n, Function.Injective u ∧ Function.Injective v ∧
      ∀ i, u i ∈ A ∧ v i ∈ B ∧ D.arc (u i) (v i) := by
  let eU : Fin U.card ≃ U := by simpa only [Fintype.card_coe] using (Fintype.equivFin U).symm
  let e : Fin U.card → Fin n := fun i => (eU i).val
  have hei : Function.Injective e := Subtype.val_injective.comp eU.injective
  have heU : ∀ i, e i ∈ U := fun i => (eU i).property
  have hes : ∀ z ∈ U, ∃ i, e i = z := by
    intro z hz
    obtain ⟨i,hi⟩ := eU.surjective ⟨z,hz⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  let F := inducedDigraph D e
  have hF : KStrong F K := kStrongOn_induced D U hU e hei heU hes rfl
  let A' := Finset.univ.filter (fun i => e i ∈ A)
  have hAsub : A ⊆ U := by rw [← hpartition]; exact Finset.subset_union_left
  have hBsub : B ⊆ U := by rw [← hpartition]; exact Finset.subset_union_right
  have hAc : A'.card = A.card := by
    apply Finset.card_bij (fun i _ => e i)
    · intro i hi; exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij; exact hei hij
    · intro z hz
      obtain ⟨i,hi⟩ := hes z (hAsub hz)
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi ▸ hz⟩,hi⟩
  have hBc : (Finset.univ \ A').card = B.card := by
    apply Finset.card_bij (fun i _ => e i)
    · intro i hi
      have hn : e i ∉ A := by simpa [A'] using (Finset.mem_sdiff.mp hi).2
      have hz := heU i
      rw [← hpartition] at hz
      exact (Finset.mem_union.mp hz).resolve_left hn
    · intro i _ j _ hij; exact hei hij
    · intro z hz
      obtain ⟨i,hi⟩ := hes z (hBsub hz)
      have hn : z ∉ A := fun ha => Finset.disjoint_left.mp hdis ha hz
      exact ⟨i,by simp [A',hi,hn],hi⟩
  obtain ⟨s,hsize,f,hfi,hf⟩ := cut_matching F hF A' hk (by omega) (by omega)
  let es : Fin s.card ≃ s := by simpa only [Fintype.card_coe] using (Fintype.equivFin s).symm
  let g : Fin k → s := fun i => es (Fin.castLE hsize i)
  have hgi : Function.Injective g := es.injective.comp (by
    intro i j hij
    exact Fin.ext (congrArg (fun q : Fin s.card => q.val) hij))
  let u := fun i => e (g i).val.val
  let v := fun i => e (f (g i))
  refine ⟨u,v,?_,hei.comp (hfi.comp hgi),?_⟩
  · exact hei.comp (Subtype.val_injective.comp (Subtype.val_injective.comp hgi))
  · intro i
    have huA : u i ∈ A := (Finset.mem_filter.mp (g i).val.property).2
    have hvi := heU (f (g i))
    rw [← hpartition] at hvi
    have hvA : v i ∉ A := by
      intro hv'
      exact (hf (g i)).1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'⟩)
    exact ⟨huA,(Finset.mem_union.mp hvi).resolve_left hvA,(hf (g i)).2⟩

end ChvatalErdos

#print axioms ChvatalErdos.induced_cut_matching
