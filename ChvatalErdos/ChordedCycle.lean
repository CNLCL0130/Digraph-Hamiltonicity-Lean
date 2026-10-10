import ChvatalErdos.PathPositions
import ChvatalErdos.LongestPath
import ChvatalErdos.DegreeCore
import Mathlib.Data.Finset.Max

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n k : Nat} {D : Digraph (Fin n)}

structure ChordedCycle (D : Digraph (Fin n)) (k : Nat) where
  length : Nat
  positive : 0 < length
  long : 2*k ≤ length
  cycle : UCycle D length
  chord : Fin length
  chord_low : 1 < chord.val
  chord_high : chord.val+1 < length
  chord_edge : TwoCycle D (cycle.vertex ⟨0,positive⟩) (cycle.vertex chord)

theorem bipartite_min_degree_chorded (D : Digraph (Fin n)) (U : Finset (Fin n))
    (hU : U.Nonempty) (hk : 3 ≤ k) (colour : Fin n → Bool)
    (hcol : ∀ u v, TwoCycle D u v → colour u ≠ colour v)
    (hdeg : ∀ v ∈ U, (k : ℝ) ≤ degreeMass D U v) :
    ∃ C : ChordedCycle D k, C.cycle.support ⊆ U := by
  obtain ⟨P,hPU,hmax⟩ := longest_path_in (D := D) U hU
  let S := Finset.univ.filter (fun i : Fin P.vertices.length => TwoCycle D P.first (P.point i))
  have hSmem : ∀ i, i ∈ S ↔ TwoCycle D P.first (P.point i) := by intro i; simp [S]
  have hScard : S.card = (U.filter (fun v => TwoCycle D P.first v)).card := by
    apply Finset.card_bij (fun i _ => P.point i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨hPU (P.point_mem i),(hSmem i).1 hi⟩
    · intro i _ j _ hij
      exact P.point_injective hij
    · intro v hv
      have hvP := longest_first_neighbours U P hPU hmax v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
      obtain ⟨i,rfl⟩ := P.point_surjective v hvP
      exact ⟨i,(hSmem i).2 (Finset.mem_filter.mp hv).2,rfl⟩
  have hkS : k ≤ S.card := by
    have hd := hdeg P.first (hPU P.first_mem)
    have he : degreeMass D U P.first = ((U.filter (fun v => TwoCycle D P.first v)).card : ℝ) := by simp [degreeMass]
    rw [he,← hScard] at hd
    exact_mod_cast hd
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  let j := S.max' hSn
  have hjS : j ∈ S := Finset.max'_mem S hSn
  have hle : ∀ i ∈ S, i.val ≤ j.val := by
    intro i hi
    exact Finset.le_max' S i hi
  have hodd : ∀ i ∈ S, i.val%2 = 1 := fun i hi => P.neighbour_point_odd colour hcol i ((hSmem i).1 hi)
  let f : S → Fin ((j.val+1)/2) := fun i => ⟨i.val.val/2,by
    have hi := hle i.val i.property
    have ho := hodd i.val i.property
    have hj := hodd j hjS
    omega⟩
  have hf : Function.Injective f := by
    intro i s his
    have he := congrArg Fin.val his
    have hi := hodd i.val i.property
    have hs := hodd s.val s.property
    apply Subtype.ext
    apply Fin.ext
    dsimp [f] at he
    omega
  have hcount : S.card ≤ (j.val+1)/2 := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hlong : 2*k ≤ j.val+1 := by omega
  have hPlen : 2 ≤ P.vertices.length := by have hj := j.isLt; omega
  let one : Fin P.vertices.length := ⟨1,by omega⟩
  have hsmall : ({one,j} : Finset (Fin P.vertices.length)).card < S.card := by
    have htwo : ({one,j} : Finset (Fin P.vertices.length)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨q,hqS,hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hqone : q.val ≠ 1 := by
    intro h
    have he : q = one := Fin.ext h
    exact hqnot (by simp [he])
  have hqj : q ≠ j := by intro he; exact hqnot (by simp [he])
  have hqlo : 1 < q.val := by have ho := hodd q hqS; omega
  have hqhi : q.val < j.val := by
    have hqle := hle q hqS
    have hne : q.val ≠ j.val := fun h => hqj (Fin.ext h)
    omega
  have hedge : TwoCycle D P.first (P.point ⟨j.val+1-1,by have hj := j.isLt; omega⟩) := by
    simpa using (hSmem j).1 hjS
  let C := P.cyclePrefix (j.val+1) (by omega) (by have hj := j.isLt; omega) hedge
  refine ⟨{
    length := j.val+1
    positive := by omega
    long := hlong
    cycle := C
    chord := ⟨q.val,by omega⟩
    chord_low := hqlo
    chord_high := by change q.val+1 < j.val+1; omega
    chord_edge := ?_ },?_⟩
  · change TwoCycle D (P.point ⟨0,_⟩) (P.point ⟨q.val,_⟩)
    rw [P.point_first]
    exact (hSmem q).1 hqS
  · exact (P.cyclePrefix_support (j.val+1) (by omega) (by have hj := j.isLt; omega) hedge).trans hPU

end ChvatalErdos

#print axioms ChvatalErdos.bipartite_min_degree_chorded
