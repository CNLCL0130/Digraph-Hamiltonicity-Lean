import ChvatalErdos.Connectivity
import Mathlib.Data.Finset.Lattice.Fold

/-!
The literal cycle-length, pancyclicity, independence-number, and vertex-
connectivity definitions used in the final section of the manuscript.
-/

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

variable {n : Nat}

/-- An injectively enumerated directed cycle of the specified length. -/
def HasCycleLength (D : Digraph (Fin n)) (len : Nat) : Prop :=
  2 ≤ len ∧ ∃ f : Fin len → Fin n, Function.Injective f ∧
    ∀ i, D.arc (f i) (f (cyclicSucc i))

/-- Directed cycles of every length from two to the order of the digraph. -/
def Pancyclic (D : Digraph (Fin n)) : Prop :=
  ∀ len : Nat, 2 ≤ len → len ≤ n → HasCycleLength D len

/-- There are no three consecutive arcs returning to their starting vertex.
Looplessness makes any such triple an actual directed triangle. -/
def TriangleFree (D : Digraph (Fin n)) : Prop :=
  ∀ x y z, D.arc x y → D.arc y z → D.arc z x → False

theorem triangleFree_not_hasCycleLength_three (D : Digraph (Fin n))
    (hD : TriangleFree D) : ¬ HasCycleLength D 3 := by
  rintro ⟨_,f,_,hf⟩
  exact hD (f 0) (f 1) (f 2)
    (by simpa [cyclicSucc] using hf 0)
    (by simpa [cyclicSucc] using hf 1)
    (by simpa [cyclicSucc] using hf 2)

theorem triangleFree_not_pancyclic (D : Digraph (Fin n))
    (hD : TriangleFree D) (hn : 3 ≤ n) : ¬ Pancyclic D := by
  intro hP
  exact triangleFree_not_hasCycleLength_three D hD (hP 3 (by omega) hn)

theorem alphaTwoLE_order (D : Digraph (Fin n)) : AlphaTwoLE D n := by
  intro xs hxs _
  have hcard := Finset.card_le_card (Finset.subset_univ xs.toFinset)
  simpa only [List.toFinset_card_of_nodup hxs,Finset.card_univ,Fintype.card_fin] using hcard

theorem alphaTwoLE_exists (D : Digraph (Fin n)) : ∃ a : Nat, AlphaTwoLE D a :=
  ⟨n,alphaTwoLE_order D⟩

/-- The actual maximum size of a set containing no directed two-cycle,
equivalently the least integer upper bound for all independent lists. -/
noncomputable def alpha₂ (D : Digraph (Fin n)) : Nat := Nat.find (alphaTwoLE_exists D)

theorem alpha₂_spec (D : Digraph (Fin n)) : AlphaTwoLE D (alpha₂ D) :=
  Nat.find_spec (alphaTwoLE_exists D)

theorem alpha₂_le_of_alphaTwoLE (D : Digraph (Fin n)) (a : Nat)
    (ha : AlphaTwoLE D a) : alpha₂ D ≤ a :=
  Nat.find_min' (alphaTwoLE_exists D) ha

theorem alphaTwoLE_iff_alpha₂_le (D : Digraph (Fin n)) (a : Nat) :
    AlphaTwoLE D a ↔ alpha₂ D ≤ a := by
  constructor
  · exact alpha₂_le_of_alphaTwoLE D a
  · intro ha xs hxs hi
    exact (alpha₂_spec D xs hxs hi).trans ha

theorem alpha₂_le_order (D : Digraph (Fin n)) : alpha₂ D ≤ n :=
  alpha₂_le_of_alphaTwoLE D n (alphaTwoLE_order D)

theorem alpha₂_pos (D : Digraph (Fin n)) (hn : 0 < n) : 0 < alpha₂ D := by
  let v : Fin n := ⟨0,hn⟩
  have hi : Independent D (fun x => x ∈ [v]) := by
    intro x y hx hy hne _
    have hxv : x = v := by simpa using hx
    have hyv : y = v := by simpa using hy
    exact hne (hxv.trans hyv.symm)
  have hbound := alpha₂_spec D [v] (by simp) hi
  simpa using hbound

theorem kStrong_mono (D : Digraph (Fin n)) {k K : Nat}
    (hD : KStrong D K) (hk : k ≤ K) : KStrong D k := by
  refine ⟨by have hn := hD.1; omega,?_⟩
  intro S hS hsize
  exact hD.2 S hS (hsize.trans_le hk)

/-- The largest integer for which the digraph is strongly connected after
every smaller vertex deletion. The finite supremum is zero when no positive
such integer exists, including disconnected digraphs and orders at most one. -/
noncomputable def connectivity (D : Digraph (Fin n)) : Nat :=
  (Finset.range (n+1)).sup (fun k => if KStrong D k then k else 0)

noncomputable abbrev κ (D : Digraph (Fin n)) : Nat := connectivity D

theorem kStrong_le_connectivity (D : Digraph (Fin n)) {m : Nat}
    (hm : KStrong D m) : m ≤ connectivity D := by
  have hmem : m ∈ Finset.range (n+1) := by
    simp only [Finset.mem_range]
    have hn := hm.1
    omega
  have hle := Finset.le_sup (f := fun k => if KStrong D k then k else 0) hmem
  simpa only [connectivity,if_pos hm] using hle

theorem connectivity_le_of_not_kStrong_succ (D : Digraph (Fin n)) (m : Nat)
    (hm : ¬ KStrong D (m+1)) : connectivity D ≤ m := by
  apply Finset.sup_le
  intro k _
  by_cases hk : KStrong D k
  · simp only [if_pos hk]
    by_contra hnot
    exact hm (kStrong_mono D hk (by omega))
  · simp only [if_neg hk]
    exact Nat.zero_le m

theorem connectivity_eq_of_kStrong_not_succ (D : Digraph (Fin n)) {m : Nat}
    (hm : KStrong D m) (hnext : ¬ KStrong D (m+1)) : connectivity D = m :=
  Nat.le_antisymm (connectivity_le_of_not_kStrong_succ D m hnext)
    (kStrong_le_connectivity D hm)

theorem connectivity_kStrong_of_pos (D : Digraph (Fin n))
    (hpos : 0 < connectivity D) : KStrong D (connectivity D) := by
  let f : Nat → Nat := fun k => if KStrong D k then k else 0
  have hnonempty : (Finset.range (n+1)).Nonempty := ⟨0,by simp⟩
  have hmem := Finset.sup_mem_of_nonempty (f := f) hnonempty
  obtain ⟨k,_,hk⟩ := hmem
  change f k = connectivity D at hk
  by_cases hstrong : KStrong D k
  · have he : k = connectivity D := by simpa [f,hstrong] using hk
    exact he ▸ hstrong
  · have he : 0 = connectivity D := by simpa [f,hstrong] using hk
    omega

theorem kStrong_iff_le_connectivity (D : Digraph (Fin n)) (m : Nat) (hm : 0 < m) :
    KStrong D m ↔ m ≤ connectivity D := by
  constructor
  · exact kStrong_le_connectivity D
  · intro hle
    exact kStrong_mono D (connectivity_kStrong_of_pos D (hm.trans_le hle)) hle

theorem connectivity_eq_zero_of_order_le_one (D : Digraph (Fin n)) (hn : n ≤ 1) :
    connectivity D = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply connectivity_le_of_not_kStrong_succ D 0
  intro h
  have hn' := h.1
  omega

theorem connectivity_eq_zero_of_not_strong (D : Digraph (Fin n))
    (hD : ¬ StrongOn D (fun _ => True)) : connectivity D = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply connectivity_le_of_not_kStrong_succ D 0
  intro h
  have hs := h.2 [] (by simp) (by simp)
  exact hD (by simpa using hs)

end ChvatalErdos

#print axioms ChvatalErdos.triangleFree_not_hasCycleLength_three
#print axioms ChvatalErdos.triangleFree_not_pancyclic
#print axioms ChvatalErdos.alphaTwoLE_iff_alpha₂_le
#print axioms ChvatalErdos.alpha₂_pos
#print axioms ChvatalErdos.kStrong_le_connectivity
#print axioms ChvatalErdos.connectivity_le_of_not_kStrong_succ
#print axioms ChvatalErdos.connectivity_eq_zero_of_not_strong
#print axioms ChvatalErdos.kStrong_iff_le_connectivity
