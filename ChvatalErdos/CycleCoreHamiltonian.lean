import ChvatalErdos.CoreSelection
import ChvatalErdos.InducedCore
import ChvatalErdos.ForestHamiltonian

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints Record
variable {n c m b l a r : Nat}

theorem hamiltonian_with_cycle_core (D : Digraph (Fin n))
    (hb : 4 ≤ b) (ha : 2 ≤ a) (hthree : ¬3 ∣ b)
    (hlmin : Nat.clog 2 a+1 ≤ l) (hlmax : l ≤ 2*a)
    (hD : KStrong D (selectionBudget a b l+r)) (hα : AlphaTwoLE D a)
    (R : Finset (Fin n)) (hR : R.card ≤ r)
    (e : Fin c → Fin n) (he : Function.Injective e)
    (heR : ∀ v, e v ∉ R) (hsurj : ∀ v, v ∉ R → ∃ w, e w = v)
    (hc : c = (Finset.univ \ R).card)
    (Q : Fin m → UCycle (inducedDigraph D e) b)
    (hQ : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z) : Hamiltonian D := by
  let F := inducedDigraph D e
  let emb := inducedEmbedding D e he
  let Q' := fun w => (Q w).mapGraph emb
  have hcore : KStrong F (selectionBudget a b l) :=
    kStrongOn_induced D (Finset.univ \ R) (kStrong_delete D hD R hR) e he
      (fun v => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,heR v⟩)
      (fun v hv => hsurj v (Finset.mem_sdiff.mp hv).2) hc
  have hm : 0 < m := by
    have hcpos : 0 < c := by have hh := hcore.1; omega
    obtain ⟨i,_,_⟩ := hcover ⟨0,hcpos⟩
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨H,hH,hHcard,hHcover⟩ := Forest.path_cover R a hα
  let ends := Forest.ends H
  let enum : Fin ends.card ≃ ends := by simpa only [Fintype.card_coe] using (Fintype.equivFin ends).symm
  let T := fun i => (enum i).val
  have hT : ends.card ≤ 2*a := (Forest.ends_card_le H).trans (Nat.mul_le_mul_left 2 hHcard)
  have hB : ∀ (outgoing : Bool) z, selectionBudget a b l ≤
      (Finset.univ.filter (fun v => if outgoing then D.arc (T z) (e v) else D.arc (e v) (T z))).card :=
    fun outgoing z => induced_neighbour_lower D hD R hR e he heR hsurj outgoing (T z)
  obtain ⟨x,hJ,hvertex,hterminal⟩ := core_selection_exists D e he Q hb (by omega) ha hthree hlmax hcore
    (alpha_induced D e he hα) hQ hcover T hT hB
  have hQ' : ∀ i k, i ≠ k → Disjoint (Q' i).support (Q' k).support := by
    intro i k hik
    rw [UCycle.support_mapGraph,UCycle.support_mapGraph]
    exact (Finset.disjoint_image he).mpr (hQ i k hik)
  have hHQ : ∀ P ∈ H, ∀ w, Disjoint P.support (Q' w).support := by
    intro P hP w
    apply Finset.disjoint_left.mpr
    intro z hzH hzQ
    have hzR := (hHcover z).1 ⟨P,hP,hzH⟩
    obtain ⟨v,hv⟩ := (Q' w).mem_support z |>.1 hzQ
    exact heR ((Q w).vertex v) (by change e ((Q w).vertex v) = z at hv; rwa [hv])
  have hspan : ∀ z, Forest.Covers H z ∨ ∃ w, z ∈ (Q' w).support := by
    intro z
    by_cases hz : z ∈ R
    · exact Or.inl ((hHcover z).2 hz)
    · obtain ⟨v,rfl⟩ := hsurj z hz
      obtain ⟨w,t,rfl⟩ := hcover v
      exact Or.inr ⟨w,(Q' w).mem_support _ |>.2 ⟨t,rfl⟩⟩
  have hneighbour : ∀ (outgoing : Bool) j z, (Forest.IsEnd H z ∨ ∃ w, z ∈ (Q' w).support) →
      a ≤ (pathNeighbours D Q' hb outgoing x j z).card := by
    intro outgoing j z hz
    rcases hz with hz | ⟨w,hz⟩
    · have hzE : z ∈ ends := (Forest.mem_ends H z).2 hz
      obtain ⟨i,hi⟩ := enum.surjective ⟨z,hzE⟩
      have hi' : T i = z := congrArg Subtype.val hi
      rw [← hi']
      exact hterminal outgoing j i
    · obtain ⟨v,rfl⟩ := (Q' w).mem_support z |>.1 hz
      exact hvertex outgoing j ((Q w).vertex v)
  exact hamiltonian_from_forest_selection D Q' hb hm x H hα hH hQ' hHQ hspan hlmin hJ
    (fun j z hz => hneighbour true j z hz) (fun j z hz => hneighbour false j z hz)

end ChvatalErdos

#print axioms ChvatalErdos.hamiltonian_with_cycle_core
