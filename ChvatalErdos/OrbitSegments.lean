import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace ChvatalErdos

theorem injective_finite_returns {V : Type} [Fintype V] (f : V → V)
    (hf : Function.Injective f) (v : V) : ∃ k : Nat, 0 < k ∧ f^[k] v = v := by
  obtain ⟨i,j,hne,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => f^[i.val] v) (by simp)
  have aux : ∀ a b : Nat, a < b → f^[a] v = f^[b] v →
      ∃ k : Nat, 0 < k ∧ f^[k] v = v := by
    intro a b hab he
    refine ⟨b-a,by omega,?_⟩
    apply hf.iterate a
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le (Nat.le_of_lt hab)]
    exact he.symm
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact aux i.val j.val hij heq
  · exact (hne (Fin.ext hij)).elim
  · exact aux j.val i.val hij heq.symm

/-- A first positive visit to the marker set. -/
structure FirstVisit {V : Type} (f : V → V) (M : V → Prop) (v : V) where
  time : Nat
  positive : 0 < time
  hit : M (f^[time] v)
  before : ∀ k, 0 < k → k < time → ¬ M (f^[k] v)

theorem firstVisit_exists {V : Type} [Fintype V] (f : V → V)
    (hf : Function.Injective f) (M : V → Prop) (v : V) (hv : M v) :
    Nonempty (FirstVisit f M v) := by
  classical
  obtain ⟨k,hk,heq⟩ := injective_finite_returns f hf v
  have hex : ∃ k : Nat, 0 < k ∧ M (f^[k] v) := ⟨k,hk,by simpa only [heq] using hv⟩
  refine ⟨⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩⟩
  intro k hk hlt hhit
  exact Nat.find_min hex hlt ⟨hk,hhit⟩

/-- Distinct marker-to-marker segments have disjoint interiors; each interior
is itself free of repetitions. The conclusion also identifies the positions. -/
theorem firstVisit_interior_injective {V : Type} {f : V → V}
    (hf : Function.Injective f) {M : V → Prop} {u v : V}
    (hu : M u) (hv : M v) (U : FirstVisit f M u) (W : FirstVisit f M v)
    {a b : Nat} (ha : 0 < a) (ha' : a < U.time)
    (hb : 0 < b) (hb' : b < W.time) (heq : f^[a] u = f^[b] v) :
    u = v ∧ a = b := by
  have hnotlt : ¬ a < b := by
    intro hab
    have hc : u = f^[b-a] v := by
      apply hf.iterate a
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (Nat.le_of_lt hab)]
      exact heq
    exact W.before (b-a) (by omega) (by omega) (hc ▸ hu)
  have hnotgt : ¬ b < a := by
    intro hba
    have hc : v = f^[a-b] u := by
      apply hf.iterate b
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (Nat.le_of_lt hba)]
      exact heq.symm
    exact U.before (a-b) (by omega) (by omega) (hc ▸ hv)
  have hab : a = b := by omega
  subst b
  exact ⟨hf.iterate a heq,rfl⟩

/-- The terminal markers of the segments are distinct as well. -/
theorem firstVisit_terminal_injective {V : Type} {f : V → V}
    (hf : Function.Injective f) {M : V → Prop} {u v : V}
    (hu : M u) (hv : M v) (U : FirstVisit f M u) (W : FirstVisit f M v)
    (heq : f^[U.time] u = f^[W.time] v) : u = v := by
  rcases lt_trichotomy U.time W.time with hlt | he | hgt
  · have hc : u = f^[W.time-U.time] v := by
      apply hf.iterate U.time
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
      exact heq
    exact (W.before _ (by omega) (by have := U.positive; omega) (hc ▸ hu)).elim
  · rw [he] at heq
    exact hf.iterate W.time heq
  · have hc : v = f^[U.time-W.time] u := by
      apply hf.iterate W.time
      rw [← Function.iterate_add_apply, Nat.add_sub_of_le (Nat.le_of_lt hgt)]
      exact heq.symm
    exact (U.before _ (by omega) (by have := W.positive; omega) (hc ▸ hv)).elim

end ChvatalErdos

#print axioms ChvatalErdos.firstVisit_exists
#print axioms ChvatalErdos.firstVisit_interior_injective
#print axioms ChvatalErdos.firstVisit_terminal_injective

