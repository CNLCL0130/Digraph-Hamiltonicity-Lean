import ChvatalErdos.DegreeCore

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat}

theorem exists_degree_core_subset (D : Digraph (Fin n)) (U₀ : Finset (Fin n)) (hU₀ : U₀.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hMass : 2*δ*U₀.card ≤ edgeMass D U₀) :
    ∃ U : Finset (Fin n), U ⊆ U₀ ∧ U.Nonempty ∧ ∀ v ∈ U, δ ≤ degreeMass D U v := by
  have hex : ∃ k : Nat, ∃ U : Finset (Fin n), U ⊆ U₀ ∧ U.Nonempty ∧ 2*δ*U.card ≤ edgeMass D U ∧ U.card = k :=
    ⟨U₀.card,U₀,Finset.Subset.refl _,hU₀,hMass,rfl⟩
  obtain ⟨U,hsub,hU,hMassU,hcard⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset (Fin n), T ⊆ U₀ → T.Nonempty → 2*δ*T.card ≤ edgeMass D T → U.card ≤ T.card := by
    intro T hTsub hT hMassT
    rw [hcard]
    exact Nat.find_min' hex ⟨T,hTsub,hT,hMassT,rfl⟩
  refine ⟨U,hsub,hU,?_⟩
  intro v hv
  by_contra hlow
  have hd : degreeMass D U v < δ := by linarith
  have hm := edgeMass_erase D U v hv
  have hc := Finset.card_erase_add_one hv
  have hcR : ((U.erase v).card : ℝ)+1 = U.card := by exact_mod_cast hc
  have hremain : 2*δ*(U.erase v).card < edgeMass D (U.erase v) := by nlinarith [hMassU,hm,hcR]
  have hne : (U.erase v).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [he,edgeMass] at hremain
  have hmin' := hmin (U.erase v) ((Finset.erase_subset v U).trans hsub) hne hremain.le
  omega

end ChvatalErdos

#print axioms ChvatalErdos.exists_degree_core_subset
