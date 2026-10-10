import ChvatalErdos.AffineObstruction

set_option autoImplicit false

namespace ChvatalErdos
namespace AffineObstruction

variable (q : Nat) [Fact q.Prime]

abbrev PointNeighbors (u : Point q) := {w : Line q // incidence q u w}
abbrev LineNeighbors (w : Line q) := {u : Point q // incidence q u w}

noncomputable instance pointNeighborsFintype (u : Point q) : Fintype (PointNeighbors q u) :=
  Fintype.ofFinite _

noncomputable instance lineNeighborsFintype (w : Line q) : Fintype (LineNeighbors q w) :=
  Fintype.ofFinite _

/-- A point has one incident line in each of the q ordinary directions,
    and one line in the vertical direction. -/
noncomputable def pointNeighborsEquiv (u : Point q) : PointNeighbors q u ≃ Option (ZMod q) where
  toFun w := w.val.1
  invFun a := ⟨(a, match a with
    | none => (pointEquiv q u).1
    | some t => (pointEquiv q u).2 - t * (pointEquiv q u).1), by
      cases a <;> simp [incidence]⟩
  left_inv w := by
    obtain ⟨⟨a, b⟩, h⟩ := w
    cases a with
    | none =>
      apply Subtype.ext
      change (none, (pointEquiv q u).1) = (none, b)
      exact Prod.ext rfl h
    | some a =>
      apply Subtype.ext
      change (some a, (pointEquiv q u).2 - a * (pointEquiv q u).1) = (some a, b)
      have hb : (pointEquiv q u).2 - a * (pointEquiv q u).1 = b :=
        sub_eq_iff_eq_add.mpr (by simpa [incidence, add_comm] using h)
      exact Prod.ext rfl hb
  right_inv a := rfl

/-- A vertical line is parametrized by y; every other line is parametrized by x. -/
noncomputable def lineNeighborsEquiv (w : Line q) : LineNeighbors q w ≃ ZMod q := by
  obtain ⟨a, b⟩ := w
  cases a with
  | none =>
    exact {
      toFun := fun u => (pointEquiv q u.val).2
      invFun := fun y => ⟨(pointEquiv q).symm (b, y), by simp [incidence]⟩
      left_inv := by
        intro u
        apply Subtype.ext
        apply (pointEquiv q).injective
        change pointEquiv q ((pointEquiv q).symm (b, (pointEquiv q u.val).2)) =
          pointEquiv q u.val
        rw [Equiv.apply_symm_apply]
        exact Prod.ext u.property.symm rfl
      right_inv := by
        intro y
        change (pointEquiv q ((pointEquiv q).symm (b, y))).2 = y
        simp }
  | some a =>
    exact {
      toFun := fun u => (pointEquiv q u.val).1
      invFun := fun x => ⟨(pointEquiv q).symm (x, a * x + b), by simp [incidence]⟩
      left_inv := by
        intro u
        apply Subtype.ext
        apply (pointEquiv q).injective
        change pointEquiv q ((pointEquiv q).symm
          ((pointEquiv q u.val).1, a * (pointEquiv q u.val).1 + b)) = pointEquiv q u.val
        rw [Equiv.apply_symm_apply]
        exact Prod.ext rfl u.property.symm
      right_inv := by
        intro x
        change (pointEquiv q ((pointEquiv q).symm (x, a * x + b))).1 = x
        simp }

theorem point_card : Fintype.card (Point q) = q * q := Fintype.card_fin _

theorem point_degree (u : Point q) : Fintype.card (PointNeighbors q u) = q + 1 := by
  rw [Fintype.card_congr (pointNeighborsEquiv q u)]
  simp [ZMod.card]

theorem line_degree (w : Line q) : Fintype.card (LineNeighbors q w) = q := by
  rw [Fintype.card_congr (lineNeighborsEquiv q w)]
  exact ZMod.card q

theorem common_line_exists (u v : Point q) :
    ∃ w : Line q, incidence q u w ∧ incidence q v w := by
  let pu := pointEquiv q u
  let pv := pointEquiv q v
  by_cases hx : pu.1 = pv.1
  · refine ⟨(none, pu.1), rfl, ?_⟩
    exact hx.symm
  · let a := (pu.2 - pv.2) / (pu.1 - pv.1)
    let b := pu.2 - a * pu.1
    refine ⟨(some a, b), ?_, ?_⟩
    · change pu.2 = a * pu.1 + (pu.2 - a * pu.1)
      ring
    · change pv.2 = a * pv.1 + (pu.2 - a * pu.1)
      have ha : a * (pu.1 - pv.1) = pu.2 - pv.2 := by
        dsimp only [a]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr hx)
      symm
      calc
        a * pv.1 + (pu.2 - a * pu.1) = pu.2 - a * (pu.1 - pv.1) := by ring
        _ = pv.2 := by rw [ha]; ring

/-- Two distinct affine points determine exactly one line. -/
theorem unique_common_line (u v : Point q) (huv : u ≠ v) :
    ∃! w : Line q, incidence q u w ∧ incidence q v w := by
  obtain ⟨w, huw, hvw⟩ := common_line_exists q u v
  refine ⟨w, ⟨huw, hvw⟩, ?_⟩
  intro z hz
  by_contra hzw
  exact no_four q u v w z huv (fun h => hzw h.symm) huw hz.1 hvw hz.2

/-- All numerical and incidence assertions of the article's affine-base lemma. -/
theorem base_properties :
    Fintype.card (Point q) = q * q ∧
    Fintype.card (Line q) = q * (q + 1) ∧
    (∀ u : Point q, Fintype.card (PointNeighbors q u) = q + 1) ∧
    (∀ w : Line q, Fintype.card (LineNeighbors q w) = q) ∧
    (∀ u v : Point q, u ≠ v → ∃! w : Line q, incidence q u w ∧ incidence q v w) ∧
    OrderedIncidence.NoFour (incidence q) ∧
    Fintype.card (Flag q) = q * q * (q + 1) :=
  ⟨point_card q, line_card q, point_degree q, line_degree q,
    unique_common_line q, no_four q, flag_card q⟩

end AffineObstruction
end ChvatalErdos

#print axioms ChvatalErdos.AffineObstruction.base_properties
