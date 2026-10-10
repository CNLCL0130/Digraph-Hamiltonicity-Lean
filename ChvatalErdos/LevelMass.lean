import ChvatalErdos.Ancestors
import ChvatalErdos.DegreeCore

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat} {D : Digraph (Fin n)} {U : Finset (Fin n)}

noncomputable def crossMass (D : Digraph (Fin n)) (A B : Finset (Fin n)) : ℝ :=
  ∑ v ∈ A, degreeMass D B v

theorem crossMass_symm (D : Digraph (Fin n)) (A B : Finset (Fin n)) : crossMass D A B = crossMass D B A := by
  unfold crossMass degreeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  have hh : TwoCycle D w v ↔ TwoCycle D v w := ⟨twoCycle_symm D,twoCycle_symm D⟩
  simp only [hh]

namespace RootedParent
variable (T : RootedParent D U)

noncomputable def level (i : Nat) : Finset (Fin n) := U.filter (fun v => T.depth v = i)

theorem mem_level (i : Nat) (v : Fin n) : v ∈ T.level i ↔ v ∈ U ∧ T.depth v = i := Finset.mem_filter

theorem level_subset (i : Nat) : T.level i ⊆ U := Finset.filter_subset _ _

theorem level_disjoint (i j : Nat) (hij : i ≠ j) : Disjoint (T.level i) (T.level j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  exact hij (((T.mem_level i v).mp hi).2.symm.trans ((T.mem_level j v).mp hj).2)

theorem level_zero : T.level 0 = {T.root} := by
  ext v
  rw [T.mem_level,Finset.mem_singleton]
  constructor
  · rintro ⟨hv,hd⟩; exact T.zero_unique v hv hd
  · rintro rfl; exact ⟨T.root_mem,T.root_depth⟩

theorem degree_layer_sum (i : Nat) (hi : 0 < i) (v : Fin n) (hv : v ∈ T.level i) :
    degreeMass D U v = degreeMass D (T.level (i-1)) v + degreeMass D (T.level i) v + degreeMass D (T.level (i+1)) v := by
  have hvU := (T.mem_level i v).mp hv |>.1
  have hvd := (T.mem_level i v).mp hv |>.2
  simp only [degreeMass,level,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases he : TwoCycle D v w
  · have hlow := T.edge_depth v hvU w hw he
    have hhigh := T.edge_depth w hw v hvU (twoCycle_symm D he)
    have hd : T.depth w = i-1 ∨ T.depth w = i ∨ T.depth w = i+1 := by omega
    rcases hd with hd | hd | hd <;> simp [he,hd,show i-1 ≠ i by omega,show i-1 ≠ i+1 by omega,show i ≠ i-1 by omega,show i+1 ≠ i-1 by omega]
  · simp [he]

theorem mass_layer_sum (i : Nat) (hi : 0 < i) :
    (∑ v ∈ T.level i, degreeMass D U v) =
      crossMass D (T.level (i-1)) (T.level i) + edgeMass D (T.level i) + crossMass D (T.level i) (T.level (i+1)) := by
  calc
    _ = ∑ v ∈ T.level i, (degreeMass D (T.level (i-1)) v + degreeMass D (T.level i) v + degreeMass D (T.level (i+1)) v) :=
      Finset.sum_congr rfl (fun v hv => T.degree_layer_sum i hi v hv)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      change crossMass D (T.level i) (T.level (i-1)) + edgeMass D (T.level i) + crossMass D (T.level i) (T.level (i+1)) = _
      rw [crossMass_symm D (T.level i) (T.level (i-1))]

theorem root_neighbour_level_one (v : Fin n) (hv : v ∈ U) : TwoCycle D T.root v ↔ T.depth v = 1 := by
  constructor
  · intro he
    have hdepth := T.edge_depth v hv T.root T.root_mem (twoCycle_symm D he)
    have hne : T.depth v ≠ 0 := by
      intro hz
      have heq := T.zero_unique v hv hz
      exact twoCycle_irrefl D T.root (heq ▸ he)
    rw [T.root_depth] at hdepth
    omega
  · intro hd
    have hparent := T.parent_depth v hv (by omega)
    have hz : T.depth (T.parent v) = 0 := by omega
    have heq := T.zero_unique (T.parent v) (T.parent_mem v hv) hz
    simpa only [heq] using T.parent_edge v hv (by omega)

theorem root_degree : degreeMass D U T.root = (T.level 1).card := by
  simp only [degreeMass,level]
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro v hv
  rw [T.root_neighbour_level_one v hv]
  split_ifs <;> norm_num

theorem cross_zero : crossMass D (T.level 0) (T.level 1) = (T.level 1).card := by
  rw [T.level_zero]
  simp only [crossMass,Finset.sum_singleton,degreeMass]
  have hh : ∀ v ∈ T.level 1, TwoCycle D T.root v := by
    intro v hv
    exact (T.root_neighbour_level_one v ((T.mem_level 1 v).mp hv).1).mpr ((T.mem_level 1 v).mp hv).2
  simp only [Finset.sum_congr rfl (fun v hv => if_pos (hh v hv)),Finset.sum_const, nsmul_eq_mul, mul_one]

end RootedParent
end ChvatalErdos

#print axioms ChvatalErdos.RootedParent.mass_layer_sum
#print axioms ChvatalErdos.RootedParent.root_degree
