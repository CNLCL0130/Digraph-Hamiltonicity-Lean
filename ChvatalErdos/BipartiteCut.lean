import ChvatalErdos.DegreeCore
import ChvatalErdos.FreshLaplace
import ChvatalErdos.MatchingSurvival
import Mathlib.Data.Finset.Max

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open FiniteProbability
variable {n : Nat}

def bipartiteCut (D : Digraph (Fin n)) (colour : Fin n → Bool) : Digraph (Fin n) where
  arc u v := D.arc u v ∧ colour u ≠ colour v
  loopless v h := D.loopless v h.1

theorem bipartiteCut_twoCycle (D : Digraph (Fin n)) (colour : Fin n → Bool) (u v : Fin n) :
    TwoCycle (bipartiteCut D colour) u v ↔ TwoCycle D u v ∧ colour u ≠ colour v := by
  simp only [TwoCycle,bipartiteCut]
  tauto

theorem bool_crossing_mean (u v : Fin n) (huv : u ≠ v) :
    expectation (fun colour : Fin n → Bool => if colour u ≠ colour v then (1 : ℝ) else 0) = 1/2 := by
  rw [expectation_coordinate_update _ u]
  simp only [Function.update_self,Function.update_of_ne huv.symm]
  have he : ∀ a : Bool,
      expectation (fun c : Bool => if a ≠ c then (1 : ℝ) else 0) = 1/2 := by
    intro a
    cases a <;> norm_num [expectation,Fintype.sum_bool]
  have he' : ∀ a : Bool, expectation (fun x : Fin n → Bool => if a ≠ x v then (1 : ℝ) else 0) = 1/2 := by
    intro a
    rw [expectation_coordinate v (fun c : Bool => if a ≠ c then (1 : ℝ) else 0)]
    exact he a
  simp_rw [he']
  exact expectation_const _

theorem bipartiteCut_mean (D : Digraph (Fin n)) (U : Finset (Fin n)) :
    expectation (fun colour : Fin n → Bool => edgeMass (bipartiteCut D colour) U) = edgeMass D U/2 := by
  simp only [edgeMass,degreeMass]
  rw [expectation_finset_sum]
  simp_rw [expectation_finset_sum]
  have he : ∀ u v, expectation (fun colour : Fin n → Bool =>
      if TwoCycle (bipartiteCut D colour) u v then (1 : ℝ) else 0) = (if TwoCycle D u v then 1 else 0)/2 := by
    intro u v
    by_cases huv : TwoCycle D u v
    · have hne : u ≠ v := fun h => D.loopless v (h ▸ huv.1)
      simp only [bipartiteCut_twoCycle,huv,true_and,if_true]
      exact bool_crossing_mean u v hne
    · simp only [bipartiteCut_twoCycle,huv,false_and,if_false]
      rw [expectation_const]
      norm_num
  simp_rw [he]
  simp only [div_eq_mul_inv,Finset.sum_mul]

theorem exists_bipartiteCut_half (D : Digraph (Fin n)) (U : Finset (Fin n)) :
    ∃ colour : Fin n → Bool, edgeMass D U/2 ≤ edgeMass (bipartiteCut D colour) U := by
  obtain ⟨colour,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun colour : Fin n → Bool => edgeMass (bipartiteCut D colour) U) Finset.univ_nonempty
  refine ⟨colour,?_⟩
  have hmean := expectation_mono (fun ω => hmax ω (Finset.mem_univ _))
  rw [bipartiteCut_mean,expectation_const] at hmean
  exact hmean

end ChvatalErdos

#print axioms ChvatalErdos.exists_bipartiteCut_half
