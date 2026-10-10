import ChvatalErdos.CyclePacking
import ChvatalErdos.CaroWei
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import ChvatalErdos.Remainder

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat}

theorem four_cycle (D : Digraph (Fin n)) (u v s t : Fin n)
    (huv : u ≠ v) (hst : s ≠ t)
    (hus : TwoCycle D u s) (hut : TwoCycle D u t)
    (hvs : TwoCycle D v s) (hvt : TwoCycle D v t) : Nonempty (UCycle D 4) := by
  have hus' : u ≠ s := fun h => D.loopless s (h ▸ hus.1)
  have hut' : u ≠ t := fun h => D.loopless t (h ▸ hut.1)
  have hvs' : v ≠ s := fun h => D.loopless s (h ▸ hvs.1)
  have hvt' : v ≠ t := fun h => D.loopless t (h ▸ hvt.1)
  let vertex : Fin 4 → Fin n := fun i => if i.val = 0 then u else if i.val = 1 then s else if i.val = 2 then v else t
  refine ⟨⟨vertex,?_,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vertex,Ne.symm]
  · intro i
    fin_cases i <;> simp_all [vertex,cyclicSucc,TwoCycle]

theorem common_neighbours_unique (D : Digraph (Fin n))
    (hfree : ∀ Q : UCycle D 4, False) (u v s t : Fin n) (hst : s ≠ t)
    (hus : TwoCycle D u s) (hut : TwoCycle D u t)
    (hvs : TwoCycle D v s) (hvt : TwoCycle D v t) : u = v := by
  by_contra huv
  obtain ⟨Q⟩ := four_cycle D u v s t huv hst hus hut hvs hvt
  exact hfree Q

noncomputable def openNeighbours (D : Digraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => TwoCycle D v w)

theorem four_cycle_wedge_count (D : Digraph (Fin n)) (hfree : ∀ Q : UCycle D 4, False) :
    ∑ v : Fin n, ((openNeighbours D v).offDiag).card ≤ n*n-n := by
  let W := Σ v : Fin n, ((openNeighbours D v).offDiag)
  let f : W → (Finset.univ : Finset (Fin n)).offDiag := fun w =>
    ⟨w.2.val,Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,(Finset.mem_offDiag.mp w.2.property).2.2⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hp : u.2.val = v.2.val := congrArg Subtype.val huv
    have hu := Finset.mem_offDiag.mp u.2.property
    have hv := Finset.mem_offDiag.mp v.2.property
    have huv' : u.1 = v.1 := by
      apply common_neighbours_unique D hfree u.1 v.1 u.2.val.1 u.2.val.2 hu.2.2
      · exact (Finset.mem_filter.mp hu.1).2
      · exact (Finset.mem_filter.mp hu.2.1).2
      · rw [hp]; exact (Finset.mem_filter.mp hv.1).2
      · rw [hp]; exact (Finset.mem_filter.mp hv.2.1).2
    cases u with | mk i u =>
      cases v with | mk j v =>
        dsimp at huv'
        subst j
        have he : u = v := Subtype.ext hp
        subst v
        rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa only [W,Fintype.card_sigma,Fintype.card_coe,Finset.offDiag_card,Finset.card_univ,Fintype.card_fin] using hc

theorem four_cycle_degree_moment (D : Digraph (Fin n)) (hfree : ∀ Q : UCycle D 4, False) :
    (∑ v : Fin n, (twoCycleDegree D v : ℝ))^2 ≤
      (n : ℝ) * ((n : ℝ)^2 + ∑ v : Fin n, (twoCycleDegree D v : ℝ)) := by
  have hw := four_cycle_wedge_count D hfree
  have hw' : ∑ v : Fin n, ((openNeighbours D v).offDiag).card ≤ n*n := hw.trans (Nat.sub_le _ _)
  have hwR : (∑ v : Fin n, (((openNeighbours D v).offDiag).card : ℝ)) ≤ (n : ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hw'
  have hcard : ∀ v, (((openNeighbours D v).offDiag).card : ℝ) = (twoCycleDegree D v : ℝ)^2 - twoCycleDegree D v := by
    intro v
    rw [Finset.offDiag_card,Nat.cast_sub (Nat.le_mul_self _)]
    simp [openNeighbours,twoCycleDegree,pow_two]
  simp_rw [hcard] at hwR
  rw [Finset.sum_sub_distrib] at hwR
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun v : Fin n => (twoCycleDegree D v : ℝ))
    (f := fun _ : Fin n => (1 : ℝ)) (g := fun v : Fin n => (twoCycleDegree D v : ℝ)^2)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => by simp)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (by linarith :
    (∑ v : Fin n, (twoCycleDegree D v : ℝ)^2) ≤ (n : ℝ)^2+∑ v : Fin n, (twoCycleDegree D v : ℝ)) (Nat.cast_nonneg _))

theorem four_cycle_degree_bound (D : Digraph (Fin n)) (hfree : ∀ Q : UCycle D 4, False) :
    (∑ v : Fin n, (twoCycleDegree D v : ℝ)) ≤ 2*(n : ℝ)^(1+1/(2 : ℝ))+32*n := by
  have hm := four_cycle_degree_moment D hfree
  by_cases hn : n = 0
  · subst n
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,zero_mul,mul_zero,add_zero]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let S := ∑ v : Fin n, (twoCycleDegree D v : ℝ)
  let μ := S/(n : ℝ)
  let q := (n : ℝ)^((2 : ℝ)⁻¹)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hμ : 0 ≤ μ := div_nonneg hS hnR.le
  have hq : 0 ≤ q := Real.rpow_nonneg hnR.le _
  have hq2 : q^2 = (n : ℝ) := Real.rpow_inv_natCast_pow hnR.le (by decide : (2 : Nat) ≠ 0)
  have hrep : S = μ*(n : ℝ) := by dsimp [μ]; field_simp
  change S^2 ≤ (n : ℝ)*((n : ℝ)^2+S) at hm
  rw [hrep] at hm
  have hm' : μ^2 ≤ (n : ℝ)+μ := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hnR)).1
    nlinarith [hm]
  have hμq : μ ≤ q+1 := by
    by_contra h
    have hdiff : 0 < μ-q-1 := by linarith
    have hsum : 0 < μ+q := by linarith
    have hh := mul_pos hdiff hsum
    nlinarith [hq2]
  have hSl : S ≤ (q+1)*(n : ℝ) := by rw [hrep]; exact mul_le_mul_of_nonneg_right hμq hnR.le
  have hpow : (n : ℝ)^(1+1/(2 : ℝ)) = (n : ℝ)*q := by
    rw [Real.rpow_add hnR,Real.rpow_one]
    simp [q,one_div]
  rw [hpow]
  have hnq := mul_nonneg hnR.le hq
  change S ≤ _
  nlinarith [hSl]

end ChvatalErdos

#print axioms ChvatalErdos.four_cycle_wedge_count
#print axioms ChvatalErdos.four_cycle_degree_bound
