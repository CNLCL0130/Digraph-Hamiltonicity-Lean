import Lean

/-!
Foundations for the supplied paper. This file is an intermediate development,
not a proof of its quantitative or asymptotic Hamiltonicity theorem.
-/

set_option autoImplicit false

namespace ChvatalErdos

structure Digraph (V : Type) where
  arc : V → V → Prop
  loopless : ∀ v, ¬ arc v v

variable {V : Type}

def TwoCycle (D : Digraph V) (u v : V) : Prop := D.arc u v ∧ D.arc v u

theorem twoCycle_symm (D : Digraph V) {u v : V}
    (h : TwoCycle D u v) : TwoCycle D v u := ⟨h.2, h.1⟩

theorem twoCycle_irrefl (D : Digraph V) (v : V) : ¬ TwoCycle D v v :=
  fun h => D.loopless v h.1

/-- Reachability inside an allowed vertex set; this includes the length-zero case. -/
inductive Reach (D : Digraph V) (allowed : V → Prop) : V → V → Prop where
  | refl {v : V} : allowed v → Reach D allowed v v
  | step {u v w : V} : Reach D allowed u v → D.arc v w → allowed w →
      Reach D allowed u w

theorem reach_start (D : Digraph V) (allowed : V → Prop) {u v : V}
    (h : Reach D allowed u v) : allowed u := by
  induction h with
  | refl hv => exact hv
  | step _ _ _ ih => exact ih

theorem reach_end (D : Digraph V) (allowed : V → Prop) {u v : V}
    (h : Reach D allowed u v) : allowed v := by
  cases h with
  | refl hv => exact hv
  | step _ _ hw => exact hw

theorem reach_trans (D : Digraph V) (allowed : V → Prop) {u v w : V}
    (huv : Reach D allowed u v) (hvw : Reach D allowed v w) :
    Reach D allowed u w := by
  induction hvw with
  | refl _ => exact huv
  | step _ he ha ih => exact Reach.step ih he ha

def StrongOn (D : Digraph V) (allowed : V → Prop) : Prop :=
  (∃ v, allowed v) ∧ ∀ u v, allowed u → allowed v → Reach D allowed u v

/-- A list is used to enumerate the deleted set, with no repeated vertices. -/
def KStrong {n : Nat} (D : Digraph (Fin n)) (K : Nat) : Prop :=
  K + 1 ≤ n ∧ ∀ S : List (Fin n), S.Nodup → S.length < K →
    StrongOn D (fun v => v ∉ S)

theorem reach_stays_left (D : Digraph V) (allowed left right : V → Prop)
    (partition : ∀ v, allowed v → left v ∨ right v)
    (no_crossing : ∀ u v, left u → right v → ¬ D.arc u v)
    {u v : V} (hu : left u) (h : Reach D allowed u v) : left v := by
  induction h with
  | refl _ => exact hu
  | @step v w _ he hw ih =>
    rcases partition w hw with hl | hr
    · exact hl
    · exact False.elim (no_crossing v w ih hr he)

theorem no_reach_across_cut (D : Digraph V) (allowed left right : V → Prop)
    (partition : ∀ v, allowed v → left v ∨ right v)
    (disjoint : ∀ v, left v → right v → False)
    (no_crossing : ∀ u v, left u → right v → ¬ D.arc u v)
    {u v : V} (hu : left u) (hv : right v) : ¬ Reach D allowed u v := by
  intro h
  exact disjoint v (reach_stays_left D allowed left right partition no_crossing hu h) hv

theorem strong_cut_has_arc (D : Digraph V) (allowed left right : V → Prop)
    (hstrong : StrongOn D allowed)
    (partition : ∀ v, allowed v → left v ∨ right v)
    (disjoint : ∀ v, left v → right v → False)
    (left_nonempty : ∃ u, allowed u ∧ left u)
    (right_nonempty : ∃ v, allowed v ∧ right v) :
    ∃ u v, left u ∧ right v ∧ D.arc u v := by
  classical
  apply Classical.byContradiction
  intro hn
  obtain ⟨u, hua, hul⟩ := left_nonempty
  obtain ⟨v, hva, hvr⟩ := right_nonempty
  have hcut : ∀ x y, left x → right y → ¬ D.arc x y := by
    intro x y hx hy hxy
    exact hn ⟨x, y, hx, hy, hxy⟩
  exact no_reach_across_cut D allowed left right partition disjoint hcut hul hvr
    (hstrong.2 u v hua hva)

theorem kStrong_cut_has_arc {n K : Nat} (D : Digraph (Fin n))
    (hstrong : KStrong D K) (S : List (Fin n))
    (hS : S.Nodup) (hsize : S.length < K)
    (left right : Fin n → Prop)
    (partition : ∀ v, v ∉ S → left v ∨ right v)
    (disjoint : ∀ v, left v → right v → False)
    (left_nonempty : ∃ u, u ∉ S ∧ left u)
    (right_nonempty : ∃ v, v ∉ S ∧ right v) :
    ∃ u v, left u ∧ right v ∧ D.arc u v :=
  strong_cut_has_arc D (fun v => v ∉ S) left right (hstrong.2 S hS hsize)
    partition disjoint left_nonempty right_nonempty

theorem strong_of_cut_property (D : Digraph V) (allowed : V → Prop)
    (nonempty : ∃ v, allowed v)
    (cut_property : ∀ left right : V → Prop,
      (∀ v, allowed v → left v ∨ right v) →
      (∀ v, left v → right v → False) →
      (∃ u, allowed u ∧ left u) →
      (∃ v, allowed v ∧ right v) →
      ∃ u v, left u ∧ right v ∧ D.arc u v) : StrongOn D allowed := by
  classical
  refine ⟨nonempty, ?_⟩
  intro u v hu hv
  apply Classical.byContradiction
  intro hnot
  let left := fun x => allowed x ∧ Reach D allowed u x
  let right := fun x => allowed x ∧ ¬ Reach D allowed u x
  have hpart : ∀ x, allowed x → left x ∨ right x := by
    intro x hx
    by_cases hr : Reach D allowed u x
    · exact Or.inl ⟨hx, hr⟩
    · exact Or.inr ⟨hx, hr⟩
  have hdis : ∀ x, left x → right x → False := fun _ hl hr => hr.2 hl.2
  obtain ⟨x, y, hx, hy, hxy⟩ := cut_property left right hpart hdis
    ⟨u, hu, hu, Reach.refl hu⟩ ⟨v, hv, hv, hnot⟩
  exact hy.2 (Reach.step hx.2 hxy hy.1)

theorem strong_iff_cut_property (D : Digraph V) (allowed : V → Prop)
    (nonempty : ∃ v, allowed v) : StrongOn D allowed ↔
    ∀ left right : V → Prop,
      (∀ v, allowed v → left v ∨ right v) →
      (∀ v, left v → right v → False) →
      (∃ u, allowed u ∧ left u) →
      (∃ v, allowed v ∧ right v) →
      ∃ u v, left u ∧ right v ∧ D.arc u v := by
  constructor
  · intro h left right hp hd hl hr
    exact strong_cut_has_arc D allowed left right h hp hd hl hr
  · exact strong_of_cut_property D allowed nonempty

/-- The two-cycle independence condition, without assuming absent one-way arcs. -/
def Independent (D : Digraph V) (I : V → Prop) : Prop :=
  ∀ u v, I u → I v → u ≠ v → ¬ TwoCycle D u v

def AlphaTwoLE (D : Digraph V) (a : Nat) : Prop :=
  ∀ xs : List V, xs.Nodup → Independent D (fun v => v ∈ xs) → xs.length ≤ a

/-- The successor in the cyclic ordering of all `n` vertex positions. -/
def cyclicSucc {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- An actual spanning directed cycle, with the paper's minimum length of two. -/
def Hamiltonian {n : Nat} (D : Digraph (Fin n)) : Prop :=
  2 ≤ n ∧ ∃ order : Fin n → Fin n,
    (∀ i j, order i = order j → i = j) ∧
    (∀ v, ∃ i, order i = v) ∧
    ∀ i, D.arc (order i) (order (cyclicSucc i))

/-- The universal property defining a sufficient connectivity bound. -/
def SufficientBound (a K : Nat) : Prop :=
  0 < K ∧ ∀ (n : Nat) (D : Digraph (Fin n)),
    AlphaTwoLE D a → KStrong D K → Hamiltonian D

def MeetsClosed (D : Digraph V) (I : V → Prop) (v : V) : Prop :=
  ∃ u, I u ∧ (v = u ∨ TwoCycle D v u)

def LeftType (D : Digraph V) (IL IR : V → Prop) (v : V) : Prop :=
  MeetsClosed D IL v ∧ ¬ MeetsClosed D IR v

def RightType (D : Digraph V) (IL IR : V → Prop) (v : V) : Prop :=
  MeetsClosed D IR v ∧ ¬ MeetsClosed D IL v

theorem left_right_exclusive (D : Digraph V) (IL IR : V → Prop) (v : V) :
    ¬ (LeftType D IL IR v ∧ RightType D IL IR v) :=
  fun h => h.1.2 h.2.1

theorem effective_exit_avoids_union (D : Digraph V) (IL IR : V → Prop) (y : V)
    (fresh_right : ∀ u, IR u → y ≠ u)
    (no_arc_right : ∀ u, IR u → ¬ D.arc y u)
    (effective : ¬ LeftType D IL IR y) :
    ¬ MeetsClosed D (fun u => IL u ∨ IR u) y := by
  have hright : ¬ MeetsClosed D IR y := by
    rintro ⟨u, hu, heq | hedge⟩
    · exact fresh_right u hu heq
    · exact no_arc_right u hu hedge.1
  have hleft : ¬ MeetsClosed D IL y := fun h => effective ⟨h, hright⟩
  rintro ⟨u, hu, hclose⟩
  rcases hu with hl | hr
  · exact hleft ⟨u, hl, hclose⟩
  · exact hright ⟨u, hr, hclose⟩

theorem effective_entrance_avoids_union (D : Digraph V) (IL IR : V → Prop) (x : V)
    (fresh_left : ∀ u, IL u → x ≠ u)
    (no_arc_left : ∀ u, IL u → ¬ D.arc u x)
    (effective : ¬ RightType D IL IR x) :
    ¬ MeetsClosed D (fun u => IL u ∨ IR u) x := by
  have hleft : ¬ MeetsClosed D IL x := by
    rintro ⟨u, hu, heq | hedge⟩
    · exact fresh_left u hu heq
    · exact no_arc_left u hu hedge.2
  have hright : ¬ MeetsClosed D IR x := fun h => effective ⟨h, hleft⟩
  rintro ⟨u, hu, hclose⟩
  rcases hu with hl | hr
  · exact hleft ⟨u, hl, hclose⟩
  · exact hright ⟨u, hr, hclose⟩

theorem independent_insert (D : Digraph V) (I : V → Prop) (x : V)
    (hi : Independent D I) (hx : ¬ MeetsClosed D I x) :
    Independent D (fun v => v = x ∨ I v) := by
  intro u v hu hv huv hedge
  rcases hu with rfl | hu
  · rcases hv with rfl | hv
    · exact huv rfl
    · exact hx ⟨v, hv, Or.inr hedge⟩
  · rcases hv with rfl | hv
    · exact hx ⟨u, hu, Or.inr (twoCycle_symm D hedge)⟩
    · exact hi u v hu hv huv hedge

/-- The combinatorial budget behind the length `2a-1` record. -/
theorem record_budget (a left_actions right_actions separator_actions : Nat)
    (ha : 1 ≤ a) (independent_budget : left_actions + right_actions ≤ a)
    (separator_budget : separator_actions < a) :
    left_actions + right_actions + separator_actions ≤ 2 * a - 1 := by
  omega

/-- Connected endpoint-pair graphs on mixed cycles supply an effective orientation.
The separate cycle-index argument must establish the hypotheses for step size three.
-/
theorem effective_pair_of_connected (E : Digraph V)
    (symmetric : ∀ u v, E.arc u v → E.arc v u)
    (neighbour : ∀ u, ∃ v, E.arc u v)
    (connected : StrongOn E (fun _ => True))
    (left right : V → Prop)
    (exclusive : ∀ v, left v → right v → False)
    (mixed_left : ¬ ∀ v, left v) (mixed_right : ¬ ∀ v, right v) :
    ∃ u v, E.arc u v ∧ ¬ right u ∧ ¬ left v := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hstep : ∀ u v, E.arc u v → ¬ right u → left v := by
    intro u v huv hru
    apply Classical.byContradiction
    intro hlv
    exact hnone ⟨u, v, huv, hru, hlv⟩
  have htyped : ∀ u, left u ∨ right u := by
    intro u
    by_cases hru : right u
    · exact Or.inr hru
    · obtain ⟨v, huv⟩ := neighbour u
      have hlv : left v := hstep u v huv hru
      have hrv : ¬ right v := exclusive v hlv
      exact Or.inl (hstep v u (symmetric u v huv) hrv)
  have hl : ∃ u, left u := by
    apply Classical.byContradiction
    intro hn
    apply mixed_right
    intro v
    rcases htyped v with hv | hv
    · exact False.elim (hn ⟨v, hv⟩)
    · exact hv
  have hr : ∃ v, right v := by
    apply Classical.byContradiction
    intro hn
    apply mixed_left
    intro v
    rcases htyped v with hv | hv
    · exact hv
    · exact False.elim (hn ⟨v, hv⟩)
  obtain ⟨u, v, hlu, hrv, huv⟩ := strong_cut_has_arc E (fun _ => True) left right
    connected (fun v _ => htyped v) exclusive
    (by obtain ⟨u, hu⟩ := hl; exact ⟨u, True.intro, hu⟩)
    (by obtain ⟨v, hv⟩ := hr; exact ⟨v, True.intro, hv⟩)
  exact exclusive v (hstep u v huv (exclusive u hlu)) hrv

end ChvatalErdos

#print axioms ChvatalErdos.kStrong_cut_has_arc
#print axioms ChvatalErdos.effective_exit_avoids_union
#print axioms ChvatalErdos.effective_entrance_avoids_union
#print axioms ChvatalErdos.independent_insert
#print axioms ChvatalErdos.record_budget
#print axioms ChvatalErdos.effective_pair_of_connected
