import ChvatalErdos.Core
import ChvatalErdos.FiniteProbability
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

namespace ChvatalErdos
open FiniteProbability
attribute [local instance] Classical.propDecidable

variable {n : Nat}

def FirstIn (s : Finset (Fin n)) (v : Fin n) (π : Equiv.Perm (Fin n)) : Prop :=
  v ∈ s ∧ ∀ w ∈ s, π v ≤ π w

theorem firstIn_unique (s : Finset (Fin n)) (v w : Fin n) (π : Equiv.Perm (Fin n))
    (hv : FirstIn s v π) (hw : FirstIn s w π) : v = w :=
  π.injective (le_antisymm (hv.2 w hw.1) (hw.2 v hv.1))

theorem firstIn_exists (s : Finset (Fin n)) (hs : s.Nonempty) (π : Equiv.Perm (Fin n)) :
    ∃ v, FirstIn s v π := by
  obtain ⟨v, hv, hmin⟩ := s.exists_min_image π hs
  exact ⟨v, hv, hmin⟩

def swapInputs (u v : Fin n) : Equiv.Perm (Equiv.Perm (Fin n)) where
  toFun π := (Equiv.swap u v).trans π
  invFun π := (Equiv.swap u v).trans π
  left_inv π := by ext w; simp
  right_inv π := by ext w; simp

theorem swap_preserves_set (s : Finset (Fin n)) (u v : Fin n) (hu : u ∈ s) (hv : v ∈ s)
    (w : Fin n) (hw : w ∈ s) : Equiv.swap u v w ∈ s := by
  by_cases hwu : w = u
  · subst w
    simpa using hv
  by_cases hwv : w = v
  · subst w
    simpa using hu
  simpa [Equiv.swap_apply_of_ne_of_ne hwu hwv] using hw

theorem firstIn_swap (s : Finset (Fin n)) (u v : Fin n) (hu : u ∈ s) (hv : v ∈ s)
    (π : Equiv.Perm (Fin n)) : FirstIn s u (swapInputs u v π) ↔ FirstIn s v π := by
  constructor
  · intro h
    refine ⟨hv, ?_⟩
    intro w hw
    have hh := h.2 (Equiv.swap u v w) (swap_preserves_set s u v hu hv w hw)
    simpa [swapInputs] using hh
  · intro h
    refine ⟨hu, ?_⟩
    intro w hw
    have hh := h.2 (Equiv.swap u v w) (swap_preserves_set s u v hu hv w hw)
    simpa [swapInputs] using hh

noncomputable def firstProb (s : Finset (Fin n)) (v : Fin n) : ℝ := by
  classical
  exact prob (Finset.univ.filter (fun π => FirstIn s v π))

theorem firstProb_eq (s : Finset (Fin n)) (u v : Fin n) (hu : u ∈ s) (hv : v ∈ s) :
    firstProb s u = firstProb s v := by
  classical
  have h := expectation_equiv (swapInputs u v)
    (fun π => if FirstIn s u π then (1 : ℝ) else 0)
  have hindicator : ∀ w, expectation (fun π => if FirstIn s w π then (1 : ℝ) else 0) =
      firstProb s w := by
    intro w
    convert indicator_expectation (Finset.univ.filter (fun π => FirstIn s w π)) using 1
    simp
  simp_rw [firstIn_swap s u v hu hv] at h
  rw [hindicator, hindicator] at h
  exact h.symm

theorem firstProb_expectation (s : Finset (Fin n)) (v : Fin n) :
    firstProb s v = expectation (fun π => if FirstIn s v π then (1 : ℝ) else 0) := by
  classical
  unfold firstProb
  rw [← indicator_expectation]
  simp

theorem expectation_finset_sum {Ω I : Type} [Fintype Ω] (s : Finset I) (f : I → Ω → ℝ) :
    expectation (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expectation (f i) := by
  unfold expectation
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem firstProb_sum (s : Finset (Fin n)) (hs : s.Nonempty) :
    (∑ v ∈ s, firstProb s v) = 1 := by
  classical
  simp_rw [firstProb_expectation]
  rw [← expectation_finset_sum]
  have hpoint : (fun π : Equiv.Perm (Fin n) => ∑ v ∈ s, if FirstIn s v π then (1 : ℝ) else 0) =
      (fun _ => 1) := by
    funext π
    obtain ⟨v, hv⟩ := firstIn_exists s hs π
    rw [Finset.sum_eq_single v]
    · simp [hv]
    · intro w hw hwv
      have hn : ¬ FirstIn s w π := fun hh => hwv (firstIn_unique s w v π hh hv)
      simp [hn]
    · exact fun h => (h hv.1).elim
  rw [hpoint, expectation_const]

theorem firstProb_value (s : Finset (Fin n)) (v : Fin n) (hv : v ∈ s) :
    firstProb s v = 1 / (s.card : ℝ) := by
  have hsum := firstProb_sum s ⟨v,hv⟩
  have heq : (∑ w ∈ s, firstProb s w) = (s.card : ℝ) * firstProb s v := by
    calc
      _ = ∑ _w ∈ s, firstProb s v := Finset.sum_congr rfl (fun w hw => firstProb_eq s w v hw hv)
      _ = _ := by simp
  rw [heq] at hsum
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨v,hv⟩).ne'
  apply (eq_div_iff hc).2
  nlinarith

noncomputable def closedNeighbours (D : Digraph (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => w = v ∨ TwoCycle D v w)

theorem mem_closed_self (D : Digraph (Fin n)) (v : Fin n) : v ∈ closedNeighbours D v := by
  simp [closedNeighbours]

noncomputable def localMinima (D : Digraph (Fin n)) (π : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => FirstIn (closedNeighbours D v) v π)

theorem localMinima_independent (D : Digraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    Independent D (fun v => v ∈ localMinima D π) := by
  intro u v hu hv huv htwo
  have hu' := (Finset.mem_filter.mp hu).2
  have hv' := (Finset.mem_filter.mp hv).2
  have huc : v ∈ closedNeighbours D u := by simp [closedNeighbours, htwo]
  have hvc : u ∈ closedNeighbours D v := by simp [closedNeighbours, twoCycle_symm D htwo]
  exact huv (π.injective (le_antisymm (hu'.2 v huc) (hv'.2 u hvc)))

theorem localMinima_card_le (D : Digraph (Fin n)) (a : Nat) (ha : AlphaTwoLE D a)
    (π : Equiv.Perm (Fin n)) : (localMinima D π).card ≤ a := by
  have h := ha (localMinima D π).toList (Finset.nodup_toList _)
    (by simpa only [Finset.mem_toList] using localMinima_independent D π)
  simpa using h

theorem caro_wei_closed (D : Digraph (Fin n)) (a : Nat) (ha : AlphaTwoLE D a) :
    (∑ v : Fin n, 1 / ((closedNeighbours D v).card : ℝ)) ≤ (a : ℝ) := by
  classical
  have hcard : ∀ π, ((localMinima D π).card : ℝ) =
      ∑ v : Fin n, if FirstIn (closedNeighbours D v) v π then (1 : ℝ) else 0 := by
    intro π
    simp only [localMinima, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  calc
    _ = ∑ v : Fin n, firstProb (closedNeighbours D v) v := by
      apply Finset.sum_congr rfl
      intro v _
      exact (firstProb_value _ v (mem_closed_self D v)).symm
    _ = expectation (fun π => ((localMinima D π).card : ℝ)) := by
      simp_rw [firstProb_expectation, hcard]
      exact (expectation_finset_sum _ _).symm
    _ ≤ (a : ℝ) := by
      rw [← expectation_const (Ω := Equiv.Perm (Fin n)) (a : ℝ)]
      apply expectation_mono
      intro π
      exact_mod_cast localMinima_card_le D a ha π

noncomputable def twoCycleDegree (D : Digraph (Fin n)) (v : Fin n) : Nat :=
  (Finset.univ.filter (fun w => TwoCycle D v w)).card

theorem closed_card_eq_degree_add_one (D : Digraph (Fin n)) (v : Fin n) :
    (closedNeighbours D v).card = twoCycleDegree D v + 1 := by
  have heq : closedNeighbours D v = insert v (Finset.univ.filter (fun w => TwoCycle D v w)) := by
    ext w
    simp [closedNeighbours]
  have hn : v ∉ Finset.univ.filter (fun w => TwoCycle D v w) := by
    simp [twoCycle_irrefl]
  rw [heq, Finset.card_insert_of_notMem hn]
  rfl

theorem caro_wei (D : Digraph (Fin n)) (a : Nat) (ha : AlphaTwoLE D a) :
    (∑ v : Fin n, 1 / ((twoCycleDegree D v : ℝ) + 1)) ≤ (a : ℝ) := by
  simpa only [closed_card_eq_degree_add_one, Nat.cast_add, Nat.cast_one] using caro_wei_closed D a ha

theorem caro_wei_density (D : Digraph (Fin n)) (a : Nat) (ha : AlphaTwoLE D a) :
    (n : ℝ) ^ 2 ≤ (a : ℝ) * ((∑ v : Fin n, (twoCycleDegree D v : ℝ)) + n) := by
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun _ : Fin n => (1 : ℝ)) (f := fun v => 1 / ((twoCycleDegree D v : ℝ) + 1))
    (g := fun v => (twoCycleDegree D v : ℝ) + 1)
    (fun v _ => by positivity) (fun v _ => by positivity)
    (fun v _ => by rw [div_mul_cancel₀ _ (by positivity)]; norm_num)
  have hsum : (∑ v : Fin n, ((twoCycleDegree D v : ℝ) + 1)) =
      (∑ v : Fin n, (twoCycleDegree D v : ℝ)) + n := by
    simp [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum] at hcauchy
  have hm := mul_le_mul_of_nonneg_right (caro_wei D a ha)
    (show 0 ≤ (∑ v : Fin n, (twoCycleDegree D v : ℝ)) + n by positivity)
  exact hcauchy.trans hm

end ChvatalErdos

#print axioms ChvatalErdos.caro_wei_closed
#print axioms ChvatalErdos.caro_wei
#print axioms ChvatalErdos.caro_wei_density
