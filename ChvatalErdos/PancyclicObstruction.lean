import ChvatalErdos.AffineObstruction
import ChvatalErdos.FourPartObstruction
import ChvatalErdos.ObstructionEstimates

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

/-- The four-copy affine-plane digraph D_q from the manuscript. -/
noncomputable def pancyclicExample (q : Nat) [Fact q.Prime] :
    Digraph (Fin (4 * (q*q*(q+1)))) :=
  fourPartDigraph (AffineObstruction.graph q)

theorem pancyclic_construction (q : Nat) (hprime : q.Prime) (hq : 11 ≤ q) :
    ∃ D : Digraph (Fin (4 * (q*q*(q+1)))),
      Hamiltonian D ∧ connectivity D = q*q*(q+1) ∧
      alpha₂ D ≤ 8*q*q+4*q-4 ∧ TriangleFree D ∧
      ¬ Pancyclic D ∧ alpha₂ D+1 ≤ connectivity D := by
  letI : Fact q.Prime := ⟨hprime⟩
  let D := pancyclicExample q
  have hqpos : 0 < q := by omega
  have hm : 0 < q*q*(q+1) := by positivity
  have hprop := fourPart_properties (AffineObstruction.graph q) hm
    (AffineObstruction.graph_alphaTwoLE q) (AffineObstruction.graph_triangleFree q)
  have hα : alpha₂ D ≤ 4*(2*q*q+q-1) :=
    alpha₂_le_of_alphaTwoLE _ _ hprop.2.2.1
  have hbudget : 4*(2*q*q+q-1) = 8*q*q+4*q-4 := by
    have hqpos : 1 ≤ q := by omega
    simp only [Nat.mul_assoc] at *
    omega
  rw [hbudget] at hα
  refine ⟨D, hprop.1, hprop.2.1, hα, hprop.2.2.2.1, hprop.2.2.2.2, ?_⟩
  have hb := obstruction_conjecture_bound q hq
  simp only [pow_two] at hb
  exact (Nat.add_le_add_right hα 1).trans
    (by simpa [D,pancyclicExample,hprop.2.1,Nat.mul_assoc] using hb)

/-- Counterexamples exist for every proposed positive linear constant. -/
theorem pancyclic_counterexample (c : ℝ) (hc : 0 < c) :
    ∃ n : Nat, ∃ D : Digraph (Fin n),
      Hamiltonian D ∧ c*(alpha₂ D : ℝ) < (connectivity D : ℝ) ∧
      ¬ Pancyclic D := by
  obtain ⟨q, hp, hq, hlarge⟩ := obstruction_prime_exists c
  obtain ⟨D, hH, hκ, hα, _, hnot, _⟩ := pancyclic_construction q hp hq
  refine ⟨_, D, hH, ?_, hnot⟩
  have hαR : (alpha₂ D : ℝ) ≤ ((8*q*q+4*q-4 : Nat) : ℝ) := by exact_mod_cast hα
  have hratio := obstruction_ratio_bound c hc q (by omega) hlarge
  simp only [pow_two] at hratio
  rw [hκ]
  exact (mul_le_mul_of_nonneg_left hαR hc.le).trans_lt
    (by simpa only [Nat.mul_assoc] using hratio)

/-- The literal negation of a universal linear connectivity criterion for pancyclicity. -/
theorem pancyclic_obstruction :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (n : Nat) (D : Digraph (Fin n)),
      Hamiltonian D → c*(alpha₂ D : ℝ) ≤ (connectivity D : ℝ) → Pancyclic D := by
  rintro ⟨c,hc,hcriterion⟩
  obtain ⟨n,D,hH,hκ,hnot⟩ := pancyclic_counterexample c hc
  exact hnot (hcriterion n D hH hκ.le)

/-- In particular the Jackson--Ordaz pancyclicity conjecture fails. -/
theorem jackson_ordaz_pancyclic_counterexample :
    ∃ n : Nat, ∃ D : Digraph (Fin n),
      Hamiltonian D ∧ alpha₂ D+1 ≤ connectivity D ∧ ¬ Pancyclic D := by
  obtain ⟨D,hH,_,_,_,hnot,hκ⟩ := pancyclic_construction 11 (by decide) (by omega)
  exact ⟨_, D, hH, hκ, hnot⟩

end ChvatalErdos

#print axioms ChvatalErdos.pancyclic_construction
#print axioms ChvatalErdos.pancyclic_counterexample
#print axioms ChvatalErdos.pancyclic_obstruction
#print axioms ChvatalErdos.jackson_ordaz_pancyclic_counterexample
