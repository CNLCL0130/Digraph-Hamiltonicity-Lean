import ChvatalErdos.PackingHamiltonian
import ChvatalErdos.Targets

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open Record

/-- The external even-cycle estimate, stated as a proposition rather than an
unproved declaration. The reduction below does not establish this proposition. -/
def EvenCycleDegreeBound (k : Nat) : Prop :=
  ∀ N : Nat, ∀ D : Digraph (Fin N), (∀ Q : UCycle D (2*k), False) →
    (∑ v : Fin N, (twoCycleDegree D v : ℝ)) ≤
      2 * ((k : ℝ)-1) * (N : ℝ)^(1+1/(k : ℝ)) + 32*((k : ℝ)-1)*(N : ℝ)

theorem maximal_remainder_bound {n a k : Nat} (D : Digraph (Fin n))
    (ha : 2 ≤ a) (hk : 2 ≤ k) (hα : AlphaTwoLE D a)
    (extremal : EvenCycleDegreeBound k)
    (P : Finset (UCycle D (2*k))) (hmax : ∀ Q : UCycle D (2*k), ¬Q.support ⊆ CyclePacking.remainder P) :
    (CyclePacking.remainder P).card ≤ remainderBudget a k := by
  let R := CyclePacking.remainder P
  let enum : Fin R.card ≃ R := by simpa only [Fintype.card_coe] using (Fintype.equivFin R).symm
  let e := fun v => (enum v).val
  have he : Function.Injective e := fun _ _ h => enum.injective (Subtype.ext h)
  let F := inducedDigraph D e
  have hfree : ∀ Q : UCycle F (2*k), False := by
    intro Q
    apply hmax (Q.mapGraph (inducedEmbedding D e he))
    intro z hz
    obtain ⟨v,hv⟩ := (Q.mapGraph (inducedEmbedding D e he)).mem_support z |>.1 hz
    have hzR := (enum (Q.vertex v)).property
    change e (Q.vertex v) = z at hv
    exact hv ▸ hzR
  have hr := remainder_from_degree_bound F (alpha_induced D e he hα) ha hk (extremal R.card F hfree)
  apply Nat.le_of_lt_succ
  have hceil := Nat.le_ceil ((2*((k : ℝ)-1)*(a : ℝ))^((k : ℝ)/((k : ℝ)-1))+
    (32*(k : ℝ)+(k : ℝ)/((k : ℝ)-1))*(a : ℝ))
  have hle : (R.card : ℝ) ≤ (remainderBudget a k : ℝ) := hr.trans hceil
  have hn : R.card ≤ remainderBudget a k := by exact_mod_cast hle
  exact Nat.lt_succ_of_le hn

theorem quantitative_of_even_cycle_bound (a k : Nat) (ha : 2 ≤ a) (hk : 2 ≤ k)
    (hthree : ¬3 ∣ k) (extremal : EvenCycleDegreeBound k) :
    SufficientBound a (remainderBudget a k + connectionBudget a k) := by
  constructor
  · have hc : 0 < colourCount a := by dsimp [colourCount]; omega
    have hK : 0 < connectionBudget a k := by dsimp [connectionBudget]; positivity
    omega
  intro n D hα hD
  obtain ⟨P,hP,hmax⟩ := CyclePacking.maximal D (2*k) (by omega)
  have hR := maximal_remainder_bound D ha hk hα extremal P hmax
  have hthree' : ¬3 ∣ 2*k := by
    intro h
    have hprime : Nat.Prime 3 := by decide
    rcases hprime.dvd_mul.mp h with h2 | hk3
    · omega
    · exact hthree hk3
  have hK : connectionBudget a k = selectionBudget a (2*k) (colourCount a) := by
    simp [connectionBudget,selectionBudget]
  apply hamiltonian_from_small_remainder D (by omega) ha hthree' (by rfl)
    (colour_count_bound a (by omega)) ?_ hα P hP hR
  simpa only [hK,colourCount,Nat.add_comm] using hD

end ChvatalErdos

#print axioms ChvatalErdos.maximal_remainder_bound
#print axioms ChvatalErdos.quantitative_of_even_cycle_bound
