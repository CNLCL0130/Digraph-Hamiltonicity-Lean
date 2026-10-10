import ChvatalErdos.CycleEndpoints
import ChvatalErdos.FiniteProbability

set_option autoImplicit false

namespace ChvatalErdos.CycleEndpoints
open FiniteProbability
attribute [local instance] Classical.propDecidable

theorem shiftThree_injective {b : Nat} (hb : 4 ≤ b) :
    Function.Injective (@shiftThree b) := by
  intro i j h
  have hij := congrArg Fin.val h
  change (i.val + 3) % b = (j.val + 3) % b at hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi' : i.val + 3 < b <;> by_cases hj' : j.val + 3 < b
  · rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hij
    omega
  · rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_sub_mod (by omega : b ≤ j.val + 3),
      Nat.mod_eq_of_lt (by omega : j.val + 3 - b < b)] at hij
    omega
  · rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_sub_mod (by omega : b ≤ i.val + 3),
      Nat.mod_eq_of_lt (by omega : i.val + 3 - b < b)] at hij
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : b ≤ i.val + 3),
      Nat.mod_eq_of_lt (by omega : i.val + 3 - b < b),
      Nat.mod_eq_sub_mod (by omega : b ≤ j.val + 3),
      Nat.mod_eq_of_lt (by omega : j.val + 3 - b < b)] at hij
    omega

noncomputable def shiftEquiv {b : Nat} (hb : 4 ≤ b) : Equiv.Perm (Fin b) :=
  Equiv.ofBijective shiftThree (Finite.injective_iff_bijective.mp (shiftThree_injective hb))

abbrev Choice (b l : Nat) := Bool × (Fin b × Fin l)

def entrance {b l : Nat} (c : Choice b l) : Fin b := c.2.1
def colour {b l : Nat} (c : Choice b l) : Fin l := c.2.2
noncomputable def exit {b l : Nat} (hb : 4 ≤ b) (c : Choice b l) : Fin b :=
  if c.1 then shiftEquiv hb c.2.1 else (shiftEquiv hb).symm c.2.1

theorem choice_card (b l : Nat) : Fintype.card (Choice b l) = 2 * b * l := by
  simp [Choice, Nat.mul_assoc]

def Effective {b l : Nat} (hb : 4 ≤ b) (left right : Fin b → Prop) (j : Fin l)
    (c : Choice b l) : Prop := colour c = j ∧ ¬ right (entrance c) ∧ ¬ left (exit hb c)

theorem exists_effective {b l : Nat} (hb : 4 ≤ b) (hthree : ¬3 ∣ b)
    (left right : Fin b → Prop) (exclusive : ∀ i, left i → right i → False)
    (mixed_left : ¬∀ i, left i) (mixed_right : ¬∀ i, right i) (j : Fin l) :
    ∃ c : Choice b l, Effective hb left right j c := by
  obtain ⟨i,k,hpair,hi,hk⟩ := mixed_cycle_has_effective_pair hb hthree left right exclusive mixed_left mixed_right
  rcases hpair with hkshift | hishift
  · refine ⟨(true,(i,j)),rfl,hi,?_⟩
    simpa [exit,shiftEquiv,hkshift] using hk
  · refine ⟨(false,(i,j)),rfl,hi,?_⟩
    have heq : (shiftEquiv hb).symm i = k := (Equiv.symm_apply_eq _).2 hishift
    simpa [exit,heq] using hk

theorem effective_probability {b l : Nat} (hb : 4 ≤ b) (hl : 0 < l) (hthree : ¬3 ∣ b)
    (left right : Fin b → Prop) (exclusive : ∀ i, left i → right i → False)
    (mixed_left : ¬∀ i, left i) (mixed_right : ¬∀ i, right i) (j : Fin l) :
    1 / ((2 * b * l : Nat) : ℝ) ≤
      prob (Finset.univ.filter (Effective hb left right j)) := by
  obtain ⟨c,hc⟩ := exists_effective hb hthree left right exclusive mixed_left mixed_right j
  have hn : (Finset.univ.filter (Effective hb left right j)).Nonempty :=
    ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩⟩
  have hcard : (1 : ℝ) ≤ (Finset.univ.filter (Effective hb left right j)).card := by
    exact_mod_cast Finset.card_pos.mpr hn
  unfold prob
  rw [choice_card]
  exact div_le_div_of_nonneg_right hcard (by positivity)

theorem endpoint_colour_probability {b l : Nat} (hb : 0 < b) (hl : 0 < l)
    (e : Bool → Equiv.Perm (Fin b)) (v : Fin b) (j : Fin l) :
    prob (Finset.univ.filter (fun c : Choice b l => e c.1 c.2.1 = v ∧ c.2.2 = j)) =
      1 / ((b : ℝ) * l) := by
  letI : NeZero b := ⟨hb.ne'⟩
  letI : NeZero l := ⟨hl.ne'⟩
  have hsingle : ∀ {r : Nat} (i : Fin r),
      expectation (fun x : Fin r => if x = i then (1 : ℝ) else 0) = 1 / (r : ℝ) := by
    intro r i
    have h := indicator_expectation ({i} : Finset (Fin r))
    simpa [prob] using h
  rw [← indicator_expectation]
  have heq : (fun c : Choice b l =>
      if c ∈ Finset.univ.filter (fun c => e c.1 c.2.1 = v ∧ c.2.2 = j) then (1 : ℝ) else 0) =
      (fun c => (if e c.1 c.2.1 = v then (1 : ℝ) else 0) *
        (if c.2.2 = j then (1 : ℝ) else 0)) := by
    funext c
    by_cases hv : e c.1 c.2.1 = v <;> by_cases hj : c.2.2 = j <;> simp [hv,hj]
  rw [heq,expectation_prod]
  simp only [expectation_prod]
  have hbase : ∀ d, expectation (fun x => if e d x = v then (1 : ℝ) else 0) = 1 / (b : ℝ) := by
    intro d
    rw [expectation_equiv (e d) (fun x => if x = v then (1 : ℝ) else 0),hsingle]
  have hinner : ∀ c : ℝ, expectation (fun x : Fin l => c * (if x = j then (1 : ℝ) else 0)) =
      c * (1 / (l : ℝ)) := by
    intro c
    rw [expectation_const_mul c (fun x : Fin l => if x = j then (1 : ℝ) else 0),hsingle]
  have hmiddle : ∀ d, expectation (fun x : Fin b =>
      (if e d x = v then (1 : ℝ) else 0) * (1 / (l : ℝ))) = (1 / (b : ℝ)) * (1 / (l : ℝ)) := by
    intro d
    rw [expectation_mul_const (fun x : Fin b => if e d x = v then (1 : ℝ) else 0) (1 / (l : ℝ)),hbase]
  calc
    _ = expectation (fun _ : Bool => (1 / (b : ℝ)) * (1 / (l : ℝ))) := by
      apply congrArg expectation
      funext d
      calc
        _ = expectation (fun x : Fin b => (if e d x = v then (1 : ℝ) else 0) * (1 / (l : ℝ))) := by
          apply congrArg expectation
          funext x
          exact hinner (if e d x = v then (1 : ℝ) else 0)
        _ = _ := hmiddle d
    _ = _ := by
      rw [expectation_const]
      simp [div_eq_mul_inv,mul_inv_rev,mul_comm]

theorem entrance_probability {b l : Nat} (hb : 0 < b) (hl : 0 < l) (v : Fin b) (j : Fin l) :
    prob (Finset.univ.filter (fun c : Choice b l => entrance c = v ∧ colour c = j)) =
      1 / ((b : ℝ) * l) :=
  endpoint_colour_probability hb hl (fun _ => Equiv.refl _) v j

theorem exit_probability {b l : Nat} (hb : 4 ≤ b) (hl : 0 < l) (v : Fin b) (j : Fin l) :
    prob (Finset.univ.filter (fun c : Choice b l => exit hb c = v ∧ colour c = j)) =
      1 / ((b : ℝ) * l) := by
  convert endpoint_colour_probability (by omega : 0 < b) hl
    (fun d => if d then shiftEquiv hb else (shiftEquiv hb).symm) v j using 1
  congr 1
  ext c
  cases h : c.1 <;> simp [exit,colour,h]

theorem offset_injective {b : Nat} (hb : 0 < b) (r : Nat) (hr : r < b) :
    Function.Injective (fun i : Fin b => index hb (i.val + r)) := by
  intro i j h
  have hij := congrArg Fin.val h
  change (i.val + r) % b = (j.val + r) % b at hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi' : i.val + r < b <;> by_cases hj' : j.val + r < b
  · rw [Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hj'] at hij
    omega
  · rw [Nat.mod_eq_of_lt hi',Nat.mod_eq_sub_mod (by omega : b ≤ j.val + r),
      Nat.mod_eq_of_lt (by omega : j.val + r - b < b)] at hij
    omega
  · rw [Nat.mod_eq_of_lt hj',Nat.mod_eq_sub_mod (by omega : b ≤ i.val + r),
      Nat.mod_eq_of_lt (by omega : i.val + r - b < b)] at hij
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : b ≤ i.val + r),Nat.mod_eq_of_lt (by omega : i.val + r - b < b),
      Nat.mod_eq_sub_mod (by omega : b ≤ j.val + r),Nat.mod_eq_of_lt (by omega : j.val + r - b < b)] at hij
    omega

noncomputable def offsetEquiv {b : Nat} (hb : 0 < b) (r : Nat) (hr : r < b) : Equiv.Perm (Fin b) :=
  Equiv.ofBijective (fun i => index hb (i.val + r))
    (Finite.injective_iff_bijective.mp (offset_injective hb r hr))

/-- The old coordinate is the retained edge's starting index. True denotes the reverse direction. -/
noncomputable def fromRetainedEdge {b l : Nat} (hb : 4 ≤ b) : Equiv.Perm (Choice b l) where
  toFun c := (c.1, ((if c.1 then offsetEquiv (by omega : 0 < b) (b - 1) (by omega)
      else offsetEquiv (by omega : 0 < b) 2 (by omega)) c.2.1, c.2.2))
  invFun c := (c.1, ((if c.1 then offsetEquiv (by omega : 0 < b) (b - 1) (by omega)
      else offsetEquiv (by omega : 0 < b) 2 (by omega)).symm c.2.1, c.2.2))
  left_inv c := by cases c with | mk d p => cases p with | mk i j => cases d <;> simp
  right_inv c := by cases c with | mk d p => cases p with | mk i j => cases d <;> simp

theorem shift_predecessor {b : Nat} (hb : 4 ≤ b) (i : Fin b) :
    shiftThree (index (by omega : 0 < b) (i.val + (b - 1))) =
      index (by omega : 0 < b) (i.val + 2) := by
  apply Fin.ext
  simp only [shiftThree,index,Nat.mod_add_mod]
  have heq : i.val + (b - 1) + 3 = i.val + 2 + b := by omega
  rw [heq,Nat.add_mod_right]

theorem retained_endpoints {b l : Nat} (hb : 4 ≤ b) (c : Choice b l) :
    let i := c.2.1
    entrance (fromRetainedEdge hb c) =
      (if c.1 then index (by omega : 0 < b) (i.val + (b-1)) else index (by omega : 0 < b) (i.val+2)) ∧
    exit hb (fromRetainedEdge hb c) =
      (if c.1 then index (by omega : 0 < b) (i.val+2) else index (by omega : 0 < b) (i.val+(b-1))) := by
  dsimp only
  cases c with
  | mk d p =>
    cases p with
    | mk i j =>
      cases d
      · constructor
        · rfl
        · change (shiftEquiv hb).symm (index (by omega : 0 < b) (i.val+2)) =
            index (by omega : 0 < b) (i.val+(b-1))
          apply (Equiv.symm_apply_eq _).2
          exact (shift_predecessor hb i).symm
      · constructor
        · rfl
        · exact shift_predecessor hb i

end ChvatalErdos.CycleEndpoints

#print axioms ChvatalErdos.CycleEndpoints.effective_probability
#print axioms ChvatalErdos.CycleEndpoints.entrance_probability
#print axioms ChvatalErdos.CycleEndpoints.exit_probability
#print axioms ChvatalErdos.CycleEndpoints.retained_endpoints
