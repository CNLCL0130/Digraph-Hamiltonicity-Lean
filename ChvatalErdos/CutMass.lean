import ChvatalErdos.LevelMass
import ChvatalErdos.BipartiteCut

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat}

theorem degreeMass_union (D : Digraph (Fin n)) (A B : Finset (Fin n))
    (hd : Disjoint A B) (v : Fin n) : degreeMass D (A ∪ B) v = degreeMass D A v + degreeMass D B v :=
  Finset.sum_union hd

theorem degreeMass_cut_same (D : Digraph (Fin n)) (A : Finset (Fin n)) (colour : Fin n → Bool)
    (c : Bool) (hA : ∀ v ∈ A, colour v = c) (v : Fin n) (hv : colour v = c) :
    degreeMass (bipartiteCut D colour) A v = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  have he : ¬TwoCycle (bipartiteCut D colour) v w := by
    intro he
    exact he.1.2 (hv.trans (hA w hw).symm)
  exact if_neg he

theorem degreeMass_cut_other (D : Digraph (Fin n)) (A : Finset (Fin n)) (colour : Fin n → Bool)
    (c : Bool) (hA : ∀ v ∈ A, colour v = c) (v : Fin n) (hv : colour v ≠ c) :
    degreeMass (bipartiteCut D colour) A v = degreeMass D A v := by
  apply Finset.sum_congr rfl
  intro w hw
  have hc : colour v ≠ colour w := by simpa only [hA w hw] using hv
  by_cases he : TwoCycle D v w
  · rw [if_pos ((bipartiteCut_twoCycle D colour v w).mpr ⟨he,hc⟩),if_pos he]
  · have hn : ¬TwoCycle (bipartiteCut D colour) v w := fun h => he ((bipartiteCut_twoCycle D colour v w).mp h).1
    rw [if_neg hn,if_neg he]

theorem cut_union_mass (D : Digraph (Fin n)) (A B : Finset (Fin n)) (hd : Disjoint A B)
    (colour : Fin n → Bool) (hA : ∀ v ∈ A, colour v = true) (hB : ∀ v ∈ B, colour v = false) :
    edgeMass (bipartiteCut D colour) (A ∪ B) = 2*crossMass D A B := by
  have hleft : ∀ v ∈ A, degreeMass (bipartiteCut D colour) (A ∪ B) v = degreeMass D B v := by
    intro v hv
    rw [degreeMass_union _ A B hd,degreeMass_cut_same D A colour true hA v (hA v hv),zero_add]
    exact degreeMass_cut_other D B colour false hB v (by simp [hA v hv])
  have hright : ∀ v ∈ B, degreeMass (bipartiteCut D colour) (A ∪ B) v = degreeMass D A v := by
    intro v hv
    rw [degreeMass_union _ A B hd,degreeMass_cut_same D B colour false hB v (hB v hv),add_zero]
    exact degreeMass_cut_other D A colour true hA v (by simp [hB v hv])
  unfold edgeMass
  rw [Finset.sum_union hd,Finset.sum_congr rfl hleft,Finset.sum_congr rfl hright]
  change crossMass D A B + crossMass D B A = _
  rw [crossMass_symm D B A]
  ring

end ChvatalErdos

#print axioms ChvatalErdos.cut_union_mass
