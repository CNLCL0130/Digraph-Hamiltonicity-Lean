import ChvatalErdos.Paths
import Mathlib.Data.Nat.Find

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n : Nat}

inductive UWalk (D : Digraph (Fin n)) (U : Finset (Fin n)) : Fin n → Fin n → Nat → Prop
  | nil {v} : v ∈ U → UWalk D U v v 0
  | step {u v w l} : UWalk D U u v l → TwoCycle D v w → w ∈ U → UWalk D U u w (l+1)

theorem UWalk.end_mem {D : Digraph (Fin n)} {U : Finset (Fin n)} {u v : Fin n} {l : Nat}
    (h : UWalk D U u v l) : v ∈ U := by cases h <;> assumption

theorem UWalk.predecessor {D : Digraph (Fin n)} {U : Finset (Fin n)} {u v : Fin n} {l : Nat}
    (h : UWalk D U u v l) (hl : 0 < l) : ∃ w, UWalk D U u w (l-1) ∧ TwoCycle D w v := by
  cases h with
  | nil _ => omega
  | step hp he _ => exact ⟨_,by simpa using hp,he⟩

noncomputable def walkComponent (D : Digraph (Fin n)) (U : Finset (Fin n)) (r : Fin n) : Finset (Fin n) :=
  U.filter (fun v => ∃ l, UWalk D U r v l)

structure RootedParent (D : Digraph (Fin n)) (U : Finset (Fin n)) where
  root : Fin n
  root_mem : root ∈ U
  depth : Fin n → Nat
  parent : Fin n → Fin n
  root_depth : depth root = 0
  zero_unique : ∀ v ∈ U, depth v = 0 → v = root
  parent_mem : ∀ v ∈ U, parent v ∈ U
  parent_depth : ∀ v ∈ U, 0 < depth v → depth (parent v)+1 = depth v
  parent_edge : ∀ v ∈ U, 0 < depth v → TwoCycle D (parent v) v
  edge_depth : ∀ u ∈ U, ∀ v ∈ U, TwoCycle D u v → depth u ≤ depth v+1

theorem component_rooted_parent (D : Digraph (Fin n)) (U : Finset (Fin n)) (r : Fin n) (hr : r ∈ U) :
    Nonempty (RootedParent D (walkComponent D U r)) := by
  let reach := fun v => ∃ l, UWalk D U r v l
  let depth := fun v => if h : reach v then Nat.find h else 0
  let C := walkComponent D U r
  have hC : ∀ v, v ∈ C ↔ v ∈ U ∧ reach v := by intro v; simp [C,walkComponent,reach]
  have hwalk : ∀ v ∈ C, UWalk D U r v (depth v) := by
    intro v hv
    have hreach := (hC v).1 hv |>.2
    dsimp [depth]
    rw [dif_pos hreach]
    exact Nat.find_spec hreach
  have hmin : ∀ v ∈ C, ∀ l, UWalk D U r v l → depth v ≤ l := by
    intro v hv l hl
    have hreach := (hC v).1 hv |>.2
    dsimp [depth]
    rw [dif_pos hreach]
    exact Nat.find_min' hreach hl
  have hrC : r ∈ C := (hC r).2 ⟨hr,⟨0,UWalk.nil hr⟩⟩
  have hrd : depth r = 0 := Nat.eq_zero_of_le_zero (hmin r hrC 0 (UWalk.nil hr))
  have hzero : ∀ v ∈ C, depth v = 0 → v = r := by
    intro v hv hz
    have h := hwalk v hv
    rw [hz] at h
    cases h
    rfl
  have hex : ∀ v ∈ C, 0 < depth v → ∃ w, w ∈ C ∧ depth w+1 = depth v ∧ TwoCycle D w v := by
    intro v hv hd
    obtain ⟨w,hw,he⟩ := (hwalk v hv).predecessor hd
    have hwC : w ∈ C := (hC w).2 ⟨hw.end_mem,⟨_,hw⟩⟩
    have hlow := hmin w hwC _ hw
    have hhigh := hmin v hv _ (UWalk.step (hwalk w hwC) he ((hC v).1 hv).1)
    exact ⟨w,hwC,by omega,he⟩
  let parent := fun v => if h : v ∈ C ∧ 0 < depth v then Classical.choose (hex v h.1 h.2) else v
  have hparent : ∀ v ∈ C, 0 < depth v → parent v ∈ C ∧ depth (parent v)+1 = depth v ∧ TwoCycle D (parent v) v := by
    intro v hv hd
    have hh := Classical.choose_spec (hex v hv hd)
    dsimp [parent]
    rw [dif_pos ⟨hv,hd⟩]
    exact hh
  refine ⟨{
    root := r
    root_mem := hrC
    depth := depth
    parent := parent
    root_depth := hrd
    zero_unique := hzero
    parent_mem := ?_
    parent_depth := fun v hv hd => (hparent v hv hd).2.1
    parent_edge := fun v hv hd => (hparent v hv hd).2.2
    edge_depth := ?_ }⟩
  · intro v hv
    by_cases hd : 0 < depth v
    · exact (hparent v hv hd).1
    · simp [parent,hd,hv]
  · intro u hu v hv he
    exact hmin u hu _ (UWalk.step (hwalk v hv) (twoCycle_symm D he) ((hC u).1 hu).1)

theorem walkComponent_neighbour (D : Digraph (Fin n)) (U : Finset (Fin n)) (r v w : Fin n)
    (hv : v ∈ walkComponent D U r) (hw : w ∈ U) (he : TwoCycle D v w) : w ∈ walkComponent D U r := by
  obtain ⟨l,hl⟩ := (Finset.mem_filter.mp hv).2
  exact Finset.mem_filter.mpr ⟨hw,⟨l+1,UWalk.step hl he hw⟩⟩

end ChvatalErdos

#print axioms ChvatalErdos.component_rooted_parent
