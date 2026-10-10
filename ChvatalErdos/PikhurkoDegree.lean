import ChvatalErdos.LevelBounds
import ChvatalErdos.PikhurkoGrowth

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n k : Nat}

theorem degreeMass_component (D : Digraph (Fin n)) (U : Finset (Fin n)) (r v : Fin n)
    (hv : v ∈ walkComponent D U r) : degreeMass D (walkComponent D U r) v = degreeMass D U v := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro w hw hn
  apply if_neg
  intro he
  exact hn (walkComponent_neighbour D U r v w hv hw he)

theorem no_even_cycle_min_degree (D : Digraph (Fin n)) (U : Finset (Fin n)) (hU : U.Nonempty)
    (hk : 3 ≤ k) (hno : ∀ Q : UCycle D (2*k), False) (δ : ℝ)
    (hdeg : ∀ v ∈ U, δ ≤ degreeMass D U v) :
    δ ≤ ((k : ℝ)-1)*(n : ℝ)^(1/(k : ℝ))+16*((k : ℝ)-1) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : 0 ≤ (n : ℝ)^(1/(k : ℝ)) := Real.rpow_nonneg (by positivity) _
  by_cases hδ : 16*((k : ℝ)-1) ≤ δ
  · obtain ⟨r,hr⟩ := hU
    let C := walkComponent D U r
    obtain ⟨T⟩ := component_rooted_parent D U r hr
    have hdegC : ∀ v ∈ C, δ ≤ degreeMass D C v := by
      intro v hv
      rw [degreeMass_component D U r v hv]
      exact hdeg v (Finset.mem_filter.mp hv).1
    let v := fun i => ((T.level i).card : ℝ)
    let E := fun i => crossMass D (T.level i) (T.level (i+1))
    apply Pikhurko.degree_bound_from_layers k (by omega) n ((k : ℝ)-1) δ (by positivity) (by linarith) hδ v E
    · intro i; exact Nat.cast_nonneg _
    · simp only [v,T.level_zero,Finset.card_singleton,Nat.cast_one]
    · exact T.cross_zero
    · change δ ≤ ((T.level 1).card : ℝ)
      rw [← T.root_degree]; exact hdegC T.root T.root_mem
    · change ((T.level k).card : ℝ) ≤ n
      have hh : (T.level k).card ≤ n := by simpa using Finset.card_le_univ (s := T.level k)
      exact_mod_cast hh
    · intro i hi hik
      have hsum : δ*(T.level i).card ≤ ∑ z ∈ T.level i, degreeMass D C z := by
        calc
          _ = ∑ z ∈ T.level i, δ := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun z hz => hdegC z (T.level_subset i hz))
      have hmass := T.mass_layer_sum i (by omega)
      have hbound := T.mass_level_bound hk hno i (by omega) hik
      rw [hmass] at hsum
      change (δ-4*((k : ℝ)-1))*(T.level i).card-crossMass D (T.level (i-1)) (T.level (i-1+1)) ≤ _
      have hiEq : i-1+1 = i := by omega
      rw [hiEq]
      dsimp [E]
      nlinarith
    · intro i hi hik
      exact T.mass_between_bound hk hno i (by omega) hik
  · have hp := mul_nonneg (show 0 ≤ (k : ℝ)-1 by linarith) hpow
    linarith

end ChvatalErdos

#print axioms ChvatalErdos.no_even_cycle_min_degree
