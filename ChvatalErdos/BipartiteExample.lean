import ChvatalErdos.PathInterval
import ChvatalErdos.LeastBound

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat}

def completeBipartite (colour : Fin n → Bool) : Digraph (Fin n) where
  arc u v := colour u ≠ colour v
  loopless _ := not_ne_iff.mpr rfl

noncomputable def colourPart (colour : Fin n → Bool) (c : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => colour v = c)

theorem completeBipartite_alpha (colour : Fin n → Bool) (a : Nat)
    (hcard : ∀ c, (colourPart colour c).card ≤ a) : AlphaTwoLE (completeBipartite colour) a := by
  intro xs hnodup hind
  by_cases hempty : xs = []
  · simp [hempty]
  obtain ⟨v,hv⟩ := List.exists_mem_of_ne_nil xs hempty
  have hsub : xs.toFinset ⊆ colourPart colour (colour v) := by
    intro w hw
    have hwm : w ∈ xs := List.mem_toFinset.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra hc
    have hne : v ≠ w := by intro he; subst w; exact hc rfl
    exact hind v w hv hwm hne ⟨fun h => hc h.symm,hc⟩
  have hh := (Finset.card_le_card hsub).trans (hcard (colour v))
  simpa only [List.toFinset_card_of_nodup hnodup] using hh

theorem completeBipartite_strong (colour : Fin n → Bool) (K : Nat) (hn : K+1 ≤ n)
    (hcard : ∀ c, K ≤ (colourPart colour c).card) : KStrong (completeBipartite colour) K := by
  refine ⟨hn,?_⟩
  intro S hS hsize
  have hex : ∀ c, ∃ v, v ∉ S ∧ colour v = c := by
    intro c
    have hc : S.toFinset.card < (colourPart colour c).card := by
      rw [List.toFinset_card_of_nodup hS]
      exact hsize.trans_le (hcard c)
    obtain ⟨v,hv,hvS⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨v,by simpa using hvS,(Finset.mem_filter.mp hv).2⟩
  obtain ⟨r,hr,_⟩ := hex false
  refine ⟨⟨r,hr⟩,?_⟩
  intro u v hu hv
  by_cases hc : colour u = colour v
  · obtain ⟨w,hw,hwc⟩ := hex (!colour u)
    have heuw : (completeBipartite colour).arc u w := by
      change colour u ≠ colour w
      rw [hwc]
      cases colour u <;> decide
    have hewv : (completeBipartite colour).arc w v := by
      change colour w ≠ colour v
      rw [← hc,hwc]
      cases colour u <;> decide
    exact Reach.step (Reach.step (Reach.refl hu) heuw hw) hewv hv
  · exact Reach.step (Reach.refl hu) hc hv

theorem completeBipartite_no_odd_hamiltonian (colour : Fin n → Bool) (hodd : n%2 = 1) :
    ¬Hamiltonian (completeBipartite colour) := by
  rintro ⟨hn,order,hinj,_,harc⟩
  let P : UPath (completeBipartite colour) := {
    vertices := List.ofFn order
    nonempty := by intro h; have hh := congrArg List.length h; simp at hh; omega
    nodup := List.nodup_ofFn.mpr hinj
    chain := by
      apply List.isChain_iff_getElem.mpr
      intro i hi
      have hi' : i+1 < n := by simpa using hi
      have he := harc ⟨i,by omega⟩
      have he' : colour (order ⟨i,by omega⟩) ≠ colour (order ⟨i+1,hi'⟩) := by
        simpa only [completeBipartite,cyclicSucc,Nat.mod_eq_of_lt hi'] using he
      simpa only [List.getElem_ofFn] using (show TwoCycle (completeBipartite colour)
        (order ⟨i,by omega⟩) (order ⟨i+1,hi'⟩) from ⟨he',he'.symm⟩) }
  have hcol := P.even_length_same_colour colour (fun _ _ he => he.1) (by simp only [P,List.length_ofFn]; omega)
  have hf : P.first = order ⟨0,by omega⟩ := by simp [P,UPath.first,List.head_eq_getElem_zero]
  have hl : P.last = order ⟨n-1,by omega⟩ := by simp [P,UPath.last,List.getLast_eq_getElem]
  rw [hf,hl] at hcol
  have he := harc ⟨n-1,by omega⟩
  have hs : cyclicSucc (⟨n-1,by omega⟩ : Fin n) = ⟨0,by omega⟩ := by
    apply Fin.ext
    change (n-1+1)%n = 0
    have hh : n-1+1 = n := by omega
    rw [hh,Nat.mod_self]
  rw [hs] at he
  exact he hcol.symm

end ChvatalErdos

#print axioms ChvatalErdos.completeBipartite_strong
#print axioms ChvatalErdos.completeBipartite_no_odd_hamiltonian
