import ChvatalErdos.LinkageHall
import ChvatalErdos.OrbitSegments
import ChvatalErdos.DirectedPaths
import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option maxRecDepth 2048

namespace ChvatalErdos

/-- Decompose a matching permutation into nonempty disjoint internal paths. -/
theorem paths_of_linkage_permutation {n r : Nat} (D : Digraph (Fin n))
    (out inn : Fin r → Finset (Fin n)) (f : Equiv.Perm (Fin n ⊕ Fin r))
    (hf : ∀ v, LinkRel D out inn v (f v)) :
    ∃ P : Fin r → DPath D, ∃ target : Equiv.Perm (Fin r),
      (∀ i, (P i).first ∈ out i ∧ (P i).last ∈ inn (target i)) ∧
      ∀ i j, i ≠ j → Disjoint (P i).support (P j).support := by
  classical
  let M : (Fin n ⊕ Fin r) → Prop := fun v => ∃ i, v = Sum.inr i
  have hM : ∀ i : Fin r, M (.inr i) := fun i => ⟨i,rfl⟩
  let U : (i : Fin r) → FirstVisit f M (.inr i) :=
    fun i => Classical.choice (firstVisit_exists f f.injective M (.inr i) (hM i))
  have htwo : ∀ i, 2 ≤ (U i).time := by
    intro i
    have hp := (U i).positive
    by_contra hn
    have ht : (U i).time = 1 := by omega
    obtain ⟨j,hj⟩ := (U i).hit
    rw [ht,Function.iterate_one] at hj
    have hh := hf (.inr i)
    rw [hj] at hh
    exact hh
  let m : Fin r → Nat := fun i => (U i).time - 1
  have hm : ∀ i, 0 < m i := by intro i; dsimp [m]; have := htwo i; omega
  have hex : ∀ i (t : Fin (m i)), ∃ v : Fin n, f^[t.val+1] (.inr i) = .inl v := by
    intro i t
    have ht : t.val+1 < (U i).time := by have := t.isLt; dsimp [m] at this; omega
    have hb := (U i).before (t.val+1) (by omega) ht
    cases he : f^[t.val+1] (.inr i) with
    | inl v => exact ⟨v,rfl⟩
    | inr j => exact (hb ⟨j,he⟩).elim
  let point : (i : Fin r) → Fin (m i) → Fin n := fun i t => Classical.choose (hex i t)
  have hat : ∀ i t, f^[t.val+1] (.inr i) = .inl (point i t) :=
    fun i t => Classical.choose_spec (hex i t)
  have hequal : ∀ i j (a : Fin (m i)) (b : Fin (m j)), point i a = point j b →
      i = j ∧ a.val = b.val := by
    intro i j a b he
    have ha : a.val+1 < (U i).time := by have := a.isLt; dsimp [m] at this; omega
    have hb : b.val+1 < (U j).time := by have := b.isLt; dsimp [m] at this; omega
    have hiter : f^[a.val+1] (.inr i) = f^[b.val+1] (.inr j) := by rw [hat,hat,he]
    obtain ⟨hij,hab⟩ := firstVisit_interior_injective f.injective
      (hM i) (hM j) (U i) (U j) (by omega) ha (by omega) hb hiter
    exact ⟨Sum.inr.inj hij,by omega⟩
  have hatinj : ∀ i, Function.Injective (point i) := by
    intro i a b he
    exact Fin.ext (hequal i i a b he).2
  have hchain : ∀ i, (List.ofFn (point i)).IsChain D.arc := by
    intro i
    apply List.isChain_iff_getElem.mpr
    intro k hk
    have hk' : k+1 < m i := by simpa using hk
    let a : Fin (m i) := ⟨k,by omega⟩
    let b : Fin (m i) := ⟨k+1,hk'⟩
    have hstep : f (.inl (point i a)) = .inl (point i b) := by
      rw [← hat i a]
      have hb := hat i b
      simpa [a,b,Function.iterate_succ_apply'] using hb
    have he := hf (.inl (point i a))
    rw [hstep] at he
    have hne : point i a ≠ point i b := by
      intro h
      have hab := congrArg Fin.val (hatinj i h)
      dsimp [a,b] at hab
      omega
    have hrel : D.arc (point i a) (point i b) := he.resolve_left hne
    simpa only [List.getElem_ofFn] using hrel
  let P : Fin r → DPath D := fun i => {
    vertices := List.ofFn (point i)
    nonempty := by intro he; have hh := congrArg List.length he; simp at hh; have := hm i; omega
    nodup := List.nodup_ofFn_ofInjective (hatinj i)
    chain := hchain i }
  let target : Fin r → Fin r := fun i => Classical.choose (U i).hit
  have htarget : ∀ i, f^[(U i).time] (.inr i) = .inr (target i) :=
    fun i => Classical.choose_spec (U i).hit
  have hinj : Function.Injective target := by
    intro i j he
    apply Sum.inr.inj
    exact firstVisit_terminal_injective f.injective (hM i) (hM j) (U i) (U j)
      (by rw [htarget,htarget,he])
  refine ⟨P,Equiv.ofBijective target ⟨hinj,Finite.surjective_of_injective hinj⟩,?_,?_⟩
  · intro i
    have hfirst : (P i).first = point i ⟨0,hm i⟩ := by simp [P,DPath.first,List.head_ofFn]
    have hlast : (P i).last = point i ⟨m i-1,by have := hm i; omega⟩ := by simp [P,DPath.last,List.getLast_ofFn]
    constructor
    · have hh := hf (.inr i)
      have hs := hat i ⟨0,hm i⟩
      simp only [Nat.zero_add,Function.iterate_one] at hs
      rw [hs] at hh
      simpa only [hfirst] using hh
    · let t : Fin (m i) := ⟨m i-1,by have := hm i; omega⟩
      have ht : t.val+1+1 = (U i).time := by dsimp [t,m]; have := htwo i; omega
      have hs : f (.inl (point i t)) = .inr (target i) := by
        rw [← hat i t,← Function.iterate_succ_apply' f (t.val+1),Nat.succ_eq_add_one,ht]
        exact htarget i
      have hh := hf (.inl (point i t))
      rw [hs] at hh
      simpa only [hlast] using hh
  · intro i j hne
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨a,ha⟩ := List.mem_ofFn.mp ((P i).mem_support v |>.1 hvi)
    obtain ⟨b,hb⟩ := List.mem_ofFn.mp ((P j).mem_support v |>.1 hvj)
    exact hne (hequal i j a b (ha.trans hb.symm)).1

/-- The set-linkage theorem needed in the paper, with the terminal incidence
relations represented by neighbour sets. Pairing is not prescribed. -/
theorem strong_set_linkage {n r h : Nat} (D : Digraph (Fin n))
    (hD : KStrong D h) (hr : r ≤ h) (out inn : Fin r → Finset (Fin n))
    (hout : ∀ i, h ≤ (out i).card) (hinn : ∀ i, h ≤ (inn i).card) :
    ∃ P : Fin r → DPath D, ∃ target : Equiv.Perm (Fin r),
      (∀ i, (P i).first ∈ out i ∧ (P i).last ∈ inn (target i)) ∧
      ∀ i j, i ≠ j → Disjoint (P i).support (P j).support := by
  obtain ⟨f,hf⟩ := linkage_permutation D hD hr out inn hout hinn
  exact paths_of_linkage_permutation D out inn f hf

end ChvatalErdos

#print axioms ChvatalErdos.strong_set_linkage





