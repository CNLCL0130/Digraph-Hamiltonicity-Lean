import ChvatalErdos.OrderedIncidence
import ChvatalErdos.PancyclicDefinitions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ChvatalErdos
namespace AffineObstruction

variable (q : Nat) [Fact q.Prime]

abbrev Point := Fin (q * q)
abbrev Line := Option (ZMod q) × ZMod q

/-- The point with index `q*x+y` has affine coordinates `(x,y)`, so the
    inherited order on `Fin (q*q)` is the article's lexicographic order. -/
noncomputable def pointEquiv : Point q ≃ ZMod q × ZMod q :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv q).toEquiv (ZMod.finEquiv q).toEquiv)

def incidence (u : Point q) (w : Line q) : Prop :=
  match w.1 with
  | none => (pointEquiv q u).1 = w.2
  | some a => (pointEquiv q u).2 = a * (pointEquiv q u).1 + w.2

abbrev Flag := OrderedIncidence.Flag (incidence q)

noncomputable def flagEquiv : Flag q ≃ Point q × Option (ZMod q) where
  toFun e := (e.val.1, e.val.2.1)
  invFun p := ⟨(p.1, (p.2, match p.2 with
    | none => (pointEquiv q p.1).1
    | some a => (pointEquiv q p.1).2 - a * (pointEquiv q p.1).1)), by
      cases p.2 <;> simp [incidence]⟩
  left_inv e := by
    obtain ⟨⟨u, ⟨a, b⟩⟩, he⟩ := e
    cases a with
    | none =>
      apply Subtype.ext
      change (u, (none, (pointEquiv q u).1)) = (u, (none, b))
      exact Prod.ext rfl (Prod.ext rfl he)
    | some a =>
      apply Subtype.ext
      change (u, (some a, (pointEquiv q u).2 - a * (pointEquiv q u).1)) =
        (u, (some a, b))
      have hb : (pointEquiv q u).2 - a * (pointEquiv q u).1 = b :=
        sub_eq_iff_eq_add.mpr (by simpa [incidence, add_comm] using he)
      exact Prod.ext rfl (Prod.ext rfl hb)
  right_inv p := rfl

theorem flag_card : Fintype.card (Flag q) = q * q * (q + 1) := by
  rw [Fintype.card_congr (flagEquiv q)]
  simp [Fintype.card_prod, ZMod.card]

theorem line_card : Fintype.card (Line q) = q * (q + 1) := by
  simp only [Fintype.card_prod, Fintype.card_option, ZMod.card]
  ring

theorem no_four : OrderedIncidence.NoFour (incidence q) := by
  intro u v w z huv hwz huw huz hvw hvz
  obtain ⟨a, b⟩ := w
  obtain ⟨c, d⟩ := z
  let pu := pointEquiv q u
  let pv := pointEquiv q v
  have point_eq (hx : pu.1 = pv.1) (hy : pu.2 = pv.2) : False :=
    huv ((pointEquiv q).injective (Prod.ext hx hy))
  cases a with
  | none =>
    change pu.1 = b at huw
    change pv.1 = b at hvw
    cases c with
    | none =>
      change pu.1 = d at huz
      exact hwz (congrArg (fun t => (none, t)) (huw.symm.trans huz))
    | some c =>
      change pu.2 = c * pu.1 + d at huz
      change pv.2 = c * pv.1 + d at hvz
      apply point_eq (huw.trans hvw.symm)
      rw [huz, hvz, huw, hvw]
  | some a =>
    change pu.2 = a * pu.1 + b at huw
    change pv.2 = a * pv.1 + b at hvw
    cases c with
    | none =>
      change pu.1 = d at huz
      change pv.1 = d at hvz
      apply point_eq (huz.trans hvz.symm)
      rw [huw, hvw, huz, hvz]
    | some c =>
      change pu.2 = c * pu.1 + d at huz
      change pv.2 = c * pv.1 + d at hvz
      by_cases hac : a = c
      · subst c
        have hb : b = d := by
          exact add_left_cancel (huw.symm.trans huz)
        exact hwz (congrArg (fun t => (some a, t)) hb)
      · have hprod : (a - c) * (pu.1 - pv.1) = 0 := by
          calc
            (a - c) * (pu.1 - pv.1) =
                ((a * pu.1 + b) - (a * pv.1 + b)) -
                  ((c * pu.1 + d) - (c * pv.1 + d)) := by ring
            _ = 0 := by rw [← huw, ← hvw, ← huz, ← hvz]; simp
        have hx : pu.1 = pv.1 := sub_eq_zero.mp
          ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hac))
        apply point_eq hx
        rw [huw, hvw, hx]

noncomputable def flagFinEquiv : Flag q ≃ Fin (q * q * (q + 1)) :=
  Fintype.equivFinOfCardEq (flag_card q)

/-- The article's graph H_q, represented as a symmetric digraph. -/
noncomputable def graph : Digraph (Fin (q * q * (q + 1))) where
  arc x y := OrderedIncidence.Adj (incidence q) ((flagFinEquiv q).symm x)
    ((flagFinEquiv q).symm y)
  loopless x := OrderedIncidence.adj_irrefl _ _

theorem graph_symmetric (x y : Fin (q * q * (q + 1))) :
    (graph q).arc x y → (graph q).arc y x :=
  OrderedIncidence.adj_symm _

theorem graph_triangleFree : TriangleFree (graph q) := by
  intro x y z hxy hyz hzx
  exact OrderedIncidence.triangle_impossible (incidence q) (no_four q)
    _ _ _ hxy hyz hzx

theorem graph_alphaTwoLE : AlphaTwoLE (graph q) (2 * q * q + q - 1) := by
  classical
  intro xs hxs hi
  let es := xs.map ((flagFinEquiv q).symm)
  have hes : es.Nodup := hxs.map (flagFinEquiv q).symm.injective
  have hbound := OrderedIncidence.independent_card_bound (incidence q) es.toFinset
    (by
      intro e he f hf haf
      have he' : e ∈ es := List.mem_toFinset.mp he
      have hf' : f ∈ es := List.mem_toFinset.mp hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf'
      have hxy : x ≠ y := by
        intro h
        subst y
        exact OrderedIncidence.adj_irrefl _ _ haf
      exact hi x y hx hy hxy ⟨haf, OrderedIncidence.adj_symm _ haf⟩)
  rw [List.toFinset_card_of_nodup hes, List.length_map] at hbound
  simp only [Fintype.card_fin, line_card] at hbound
  have heq : q * q + q * (q + 1) = 2 * q * q + q := by ring
  rw [heq] at hbound
  exact hbound

end AffineObstruction
end ChvatalErdos

#print axioms ChvatalErdos.AffineObstruction.graph_triangleFree
#print axioms ChvatalErdos.AffineObstruction.graph_alphaTwoLE
