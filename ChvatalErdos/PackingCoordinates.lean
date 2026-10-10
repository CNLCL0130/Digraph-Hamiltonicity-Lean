import ChvatalErdos.NormalRecords
import ChvatalErdos.Connectivity

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
variable {n m b : Nat}

theorem coordinate_injective (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support) :
    Function.Injective (fun p : Fin m × Fin b => (Q p.1).vertex p.2) := by
  intro p q he
  change (Q p.1).vertex p.2 = (Q q.1).vertex q.2 at he
  have hi : p.1 = q.1 := by
    by_contra hn
    exact Finset.disjoint_left.mp (hdis p.1 q.1 hn)
      ((Q p.1).mem_support _ |>.2 ⟨p.2,rfl⟩)
      ((Q q.1).mem_support _ |>.2 ⟨q.2,he.symm⟩)
  apply Prod.ext hi
  rw [hi] at he
  exact (Q q.1).injective he

theorem verticesOf_card (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support) (I : Finset (Fin m)) :
    (verticesOf D Q I).card = I.card*b := by
  unfold verticesOf
  rw [Finset.card_biUnion (by intro i hi k hk hik; exact hdis i k hik)]
  simp [(Q _).card_support]

theorem verticesOf_disjoint (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (I J : Finset (Fin m)) (hIJ : Disjoint I J) : Disjoint (verticesOf D Q I) (verticesOf D Q J) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨k,hk,hzk⟩ := Finset.mem_biUnion.mp hz'
  have hik : i ≠ k := fun he => Finset.disjoint_left.mp hIJ (he ▸ hi) hk
  exact Finset.disjoint_left.mp (hdis i k hik) hzi hzk

theorem normal_vertex_partition (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) (s : State n m) (hn : mixed D Q s = ∅) :
    observed D Q s ∪ verticesOf D Q (pureLeft D Q s) ∪ verticesOf D Q (pureRight D Q s) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro z
  obtain ⟨i,t,rfl⟩ := hcover z
  rcases normal_partition D Q s hn i with hi | hi | hi
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (vertex_in_verticesOf D Q _ i hi t))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (vertex_in_verticesOf D Q _ i hi t))
  · exact Finset.mem_union_right _ (vertex_in_verticesOf D Q _ i hi t)

theorem coordinate_count (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (I : Finset (Fin m)) (P : Fin n → Prop) :
    ∑ i : Fin m, (if i ∈ I then (Finset.univ.filter (fun t => P ((Q i).vertex t))).card else 0) =
      ((verticesOf D Q I).filter P).card := by
  let B := fun i => if i ∈ I then Finset.univ.filter (fun t => P ((Q i).vertex t)) else ∅
  let A := fun i => (B i).image (Q i).vertex
  have hAc : ∀ i, (A i).card = if i ∈ I then (Finset.univ.filter (fun t => P ((Q i).vertex t))).card else 0 := by
    intro i
    rw [Finset.card_image_of_injective _ (Q i).injective]
    dsimp [B]
    split <;> simp
  have hA : ∀ i, A i ⊆ (Q i).support := by
    intro i z hz
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact (Q i).mem_support _ |>.2 ⟨t,rfl⟩
  have heq : Finset.univ.biUnion A = (verticesOf D Q I).filter P := by
    ext z
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
      have hit : i ∈ I := by by_contra hn; simp [B,hn] at ht
      have hp : P ((Q i).vertex t) := by simpa [B,hit] using ht
      exact ⟨vertex_in_verticesOf D Q I i hit t,hp⟩
    · rintro ⟨hz,hP⟩
      obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨t,ht⟩ := (Q i).mem_support z |>.1 hzi
      exact ⟨i,Finset.mem_image.mpr ⟨t,by simp [B,hi,ht,hP],ht⟩⟩
  rw [← heq,Finset.card_biUnion (by intro i hi k hk hik; exact (hdis i k hik).mono (hA i) (hA k))]
  exact Finset.sum_congr rfl (fun i _ => (hAc i).symm)

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.coordinate_count
