import ChvatalErdos.GraphEmbedding
import ChvatalErdos.Connectivity

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n c a K r : Nat}

theorem alpha_induced (D : Digraph (Fin n)) (e : Fin c → Fin n) (he : Function.Injective e)
    (hα : AlphaTwoLE D a) : AlphaTwoLE (inducedDigraph D e) a := by
  intro xs hn hi
  have hmap : Independent D (fun v => v ∈ xs.map e) := by
    rintro u v hu hv huv hcycle
    obtain ⟨u',hu',rfl⟩ := List.mem_map.mp hu
    obtain ⟨v',hv',rfl⟩ := List.mem_map.mp hv
    exact hi u' v' hu' hv' (fun h => huv (congrArg e h)) hcycle
  simpa using hα (xs.map e) (hn.map he) hmap

theorem induced_neighbour_count (D : Digraph (Fin n)) (e : Fin c → Fin n) (he : Function.Injective e)
    (R : Finset (Fin n)) (heR : ∀ v, e v ∉ R) (hsurj : ∀ v, v ∉ R → ∃ w, e w = v)
    (outgoing : Bool) (z : Fin n) :
    (Finset.univ.filter (fun v => if outgoing then D.arc z (e v) else D.arc (e v) z)).card =
      ((if outgoing then outNeighbours D z else inNeighbours D z) \ R).card := by
  apply Finset.card_bij (fun v _ => e v)
  · intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨?_,heR v⟩
    cases outgoing <;> simpa [outNeighbours,inNeighbours] using (Finset.mem_filter.mp hv).2
  · intro v _ w _ hvw
    exact he hvw
  · intro v hv
    obtain ⟨w,rfl⟩ := hsurj v (Finset.mem_sdiff.mp hv).2
    refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    cases outgoing <;> simpa [outNeighbours,inNeighbours] using (Finset.mem_sdiff.mp hv).1

theorem induced_neighbour_lower (D : Digraph (Fin n)) (hD : KStrong D (K+r))
    (R : Finset (Fin n)) (hR : R.card ≤ r) (e : Fin c → Fin n) (he : Function.Injective e)
    (heR : ∀ v, e v ∉ R) (hsurj : ∀ v, v ∉ R → ∃ w, e w = v)
    (outgoing : Bool) (z : Fin n) :
    K ≤ (Finset.univ.filter (fun v => if outgoing then D.arc z (e v) else D.arc (e v) z)).card := by
  rw [induced_neighbour_count D e he R heR hsurj]
  cases outgoing
  · exact kStrong_outside_indegree D hD R hR z
  · exact kStrong_outside_outdegree D hD R hR z

end ChvatalErdos

#print axioms ChvatalErdos.alpha_induced
#print axioms ChvatalErdos.induced_neighbour_lower
