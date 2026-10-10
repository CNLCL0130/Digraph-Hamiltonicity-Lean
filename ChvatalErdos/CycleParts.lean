import ChvatalErdos.CyclePacking

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.UCycle
variable {n b : Nat} {D : Digraph (Fin n)}

theorem bipartite_part_many (Q : UCycle D b) (hb : 4 ≤ b) (colour : Fin n → Bool)
    (hcol : ∀ i, colour (Q.vertex i) ≠ colour (Q.vertex (cyclicSucc i))) (c : Bool) :
    1 < (Q.support.filter (fun v => colour v = c)).card := by
  let v₀ := Q.vertex ⟨0,by omega⟩
  let v₁ := Q.vertex ⟨1,by omega⟩
  let v₂ := Q.vertex ⟨2,by omega⟩
  let v₃ := Q.vertex ⟨3,by omega⟩
  have h01 : colour v₀ ≠ colour v₁ := by
    have h := hcol ⟨0,by omega⟩
    simpa only [cyclicSucc,Nat.zero_add,Nat.mod_eq_of_lt (by omega : 1 < b)] using h
  have h12 : colour v₁ ≠ colour v₂ := by
    have h := hcol ⟨1,by omega⟩
    simpa only [cyclicSucc,Nat.mod_eq_of_lt (by omega : 2 < b)] using h
  have h23 : colour v₂ ≠ colour v₃ := by
    have h := hcol ⟨2,by omega⟩
    simpa only [cyclicSucc,Nat.mod_eq_of_lt (by omega : 3 < b)] using h
  have h02 : colour v₀ = colour v₂ := by cases h0 : colour v₀ <;> cases h1 : colour v₁ <;> cases h2 : colour v₂ <;> simp_all
  have h13 : colour v₁ = colour v₃ := by cases h1 : colour v₁ <;> cases h2 : colour v₂ <;> cases h3 : colour v₃ <;> simp_all
  have hpair : ∀ (x y : Fin b), x ≠ y → colour (Q.vertex x) = c → colour (Q.vertex y) = c →
      1 < (Q.support.filter (fun v => colour v = c)).card := by
    intro x y hxy hx hy
    have hne : Q.vertex x ≠ Q.vertex y := fun h => hxy (Q.injective h)
    have hsub : {Q.vertex x,Q.vertex y} ⊆ Q.support.filter (fun v => colour v = c) := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_filter.mpr ⟨(Q.mem_support _).mpr ⟨x,rfl⟩,hx⟩
      · have hv := Finset.mem_singleton.mp hv
        subst v
        exact Finset.mem_filter.mpr ⟨(Q.mem_support _).mpr ⟨y,rfl⟩,hy⟩
    have hh := Finset.card_le_card hsub
    simpa [hne] using (show 2 ≤ (Q.support.filter (fun v => colour v = c)).card by simpa [hne] using hh)
  by_cases hc : colour v₀ = c
  · exact hpair ⟨0,by omega⟩ ⟨2,by omega⟩ (by intro h; have hh := congrArg Fin.val h; simp at hh) hc (h02.symm.trans hc)
  · have hc1 : colour v₁ = c := by cases h0 : colour v₀ <;> cases h1 : colour v₁ <;> cases c <;> simp_all
    exact hpair ⟨1,by omega⟩ ⟨3,by omega⟩ (by intro h; have hh := congrArg Fin.val h; simp at hh) hc1 (h13.symm.trans hc1)

end ChvatalErdos.UCycle

#print axioms ChvatalErdos.UCycle.bipartite_part_many
