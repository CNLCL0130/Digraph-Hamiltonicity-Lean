import ChvatalErdos.Forest
import ChvatalErdos.CyclePacking

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat} {D : Digraph (Fin n)}

theorem UPath.support_card (P : UPath D) : P.support.card = P.vertices.length := by
  exact List.toFinset_card_of_nodup P.nodup

theorem longest_path_in (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ P : UPath D, P.support ⊆ U ∧
      ∀ Q : UPath D, Q.support ⊆ U → Q.vertices.length ≤ P.vertices.length := by
  have hex : ∃ k : Nat, ∃ P : UPath D, P.support ⊆ U ∧ U.card-P.vertices.length = k := by
    obtain ⟨v,hv⟩ := hU
    refine ⟨U.card-1,Forest.singletonPath v,?_,rfl⟩
    simpa [Forest.singletonPath,UPath.support] using hv
  obtain ⟨P,hP,hcard⟩ := Nat.find_spec hex
  refine ⟨P,hP,?_⟩
  intro Q hQ
  have hmin : U.card-P.vertices.length ≤ U.card-Q.vertices.length := by
    rw [hcard]
    exact Nat.find_min' hex ⟨Q,hQ,rfl⟩
  have hp := Finset.card_le_card hP
  have hq := Finset.card_le_card hQ
  rw [UPath.support_card] at hp hq
  omega

theorem longest_first_neighbours (U : Finset (Fin n)) (P : UPath D)
    (hP : P.support ⊆ U)
    (hmax : ∀ Q : UPath D, Q.support ⊆ U → Q.vertices.length ≤ P.vertices.length)
    (v : Fin n) (hv : v ∈ U) (he : TwoCycle D P.first v) : v ∈ P.support := by
  by_contra hvP
  let S : UPath D := Forest.singletonPath v
  have hdis : Disjoint S.support P.support := by simpa [S,Forest.singletonPath,UPath.support] using hvP
  have hedge : TwoCycle D S.last P.first := twoCycle_symm D he
  let Q := S.join P hdis hedge
  have hQU : Q.support ⊆ U := by
    rw [UPath.support_join]
    apply Finset.union_subset ?_ hP
    simpa [S,Forest.singletonPath,UPath.support] using hv
  have hlen := hmax Q hQU
  simp [Q,UPath.join,S,Forest.singletonPath] at hlen

end ChvatalErdos

#print axioms ChvatalErdos.longest_first_neighbours
