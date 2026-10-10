import ChvatalErdos.CaroWei
import Mathlib.Data.Nat.Find

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat}

noncomputable def degreeMass (D : Digraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) : ℝ :=
  ∑ w ∈ U, if TwoCycle D v w then 1 else 0

noncomputable def edgeMass (D : Digraph (Fin n)) (U : Finset (Fin n)) : ℝ :=
  ∑ v ∈ U, degreeMass D U v

theorem degreeMass_nonneg (D : Digraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) :
    0 ≤ degreeMass D U v := by dsimp [degreeMass]; positivity

theorem degreeMass_insert (D : Digraph (Fin n)) (U : Finset (Fin n)) (v w : Fin n) (hv : v ∉ U) :
    degreeMass D (insert v U) w = degreeMass D U w + if TwoCycle D w v then 1 else 0 := by
  simp only [degreeMass,Finset.sum_insert hv,add_comm]

theorem edgeMass_insert (D : Digraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) (hv : v ∉ U) :
    edgeMass D (insert v U) = edgeMass D U + 2*degreeMass D U v := by
  have hs : ∀ w, TwoCycle D w v ↔ TwoCycle D v w := by intro w; exact ⟨twoCycle_symm D,twoCycle_symm D⟩
  simp only [edgeMass,Finset.sum_insert hv,degreeMass_insert D U v _ hv,twoCycle_irrefl,if_false,add_zero,
    Finset.sum_add_distrib,hs]
  change degreeMass D U v + (edgeMass D U + degreeMass D U v) = _
  dsimp [edgeMass]
  ring

theorem edgeMass_erase (D : Digraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) (hv : v ∈ U) :
    edgeMass D U = edgeMass D (U.erase v)+2*degreeMass D U v := by
  have h := edgeMass_insert D (U.erase v) v (Finset.notMem_erase v U)
  have hd := degreeMass_insert D (U.erase v) v v (Finset.notMem_erase v U)
  rw [Finset.insert_erase hv] at h hd
  simp only [twoCycle_irrefl,if_false,add_zero] at hd
  rw [hd]
  exact h

theorem exists_degree_core (D : Digraph (Fin n)) (δ : ℝ) (hδ : 0 < δ)
    (hn : 0 < n) (hMass : 2*δ*n ≤ edgeMass D Finset.univ) :
    ∃ U : Finset (Fin n), U.Nonempty ∧ ∀ v ∈ U, δ ≤ degreeMass D U v := by
  have hex : ∃ k : Nat, ∃ U : Finset (Fin n), U.Nonempty ∧ 2*δ*U.card ≤ edgeMass D U ∧ U.card = k :=
    ⟨n,Finset.univ,⟨⟨0,hn⟩,Finset.mem_univ _⟩,by simpa using hMass,by simp⟩
  obtain ⟨U,hU,hMassU,hcard⟩ := Nat.find_spec hex
  have hmin : ∀ T : Finset (Fin n), T.Nonempty → 2*δ*T.card ≤ edgeMass D T → U.card ≤ T.card := by
    intro T hT hMassT
    rw [hcard]
    exact Nat.find_min' hex ⟨T,hT,hMassT,rfl⟩
  refine ⟨U,hU,?_⟩
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
  have hmin' := hmin (U.erase v) hne hremain.le
  omega

end ChvatalErdos

#print axioms ChvatalErdos.exists_degree_core
