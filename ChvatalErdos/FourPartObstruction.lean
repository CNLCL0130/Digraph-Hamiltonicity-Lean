import ChvatalErdos.PancyclicDefinitions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

def fourPart {m : Nat} (v : Fin (4 * m)) : Fin 4 :=
  ⟨v.val % 4, Nat.mod_lt _ (by decide)⟩

def fourLocal {m : Nat} (v : Fin (4 * m)) : Fin m :=
  ⟨v.val / 4, by have h := v.isLt; omega⟩

def fourVertex {m : Nat} (p : Fin 4) (v : Fin m) : Fin (4 * m) :=
  ⟨4 * v.val + p.val, by have hp := p.isLt; have hv := v.isLt; omega⟩

@[simp] theorem fourPart_vertex {m : Nat} (p : Fin 4) (v : Fin m) :
    fourPart (fourVertex p v) = p := by
  apply Fin.ext
  simp [fourPart, fourVertex, Nat.add_mod, Nat.mod_eq_of_lt p.isLt]

@[simp] theorem fourLocal_vertex {m : Nat} (p : Fin 4) (v : Fin m) :
    fourLocal (fourVertex p v) = v := by
  apply Fin.ext
  change (4*v.val+p.val)/4 = v.val
  have hp := p.isLt
  omega

theorem fourVertex_injective {m : Nat} (p : Fin 4) :
    Function.Injective (fourVertex (m := m) p) := by
  intro u v huv
  simpa using congrArg fourLocal huv

theorem four_coordinates_injective {m : Nat} {u v : Fin (4*m)}
    (hp : fourPart u = fourPart v) (hl : fourLocal u = fourLocal v) : u = v := by
  apply Fin.ext
  have hp' := congrArg Fin.val hp
  have hl' := congrArg Fin.val hl
  simp only [fourPart, fourLocal] at hp' hl'
  omega

@[simp] theorem fourVertex_coordinates {m : Nat} (u : Fin (4*m)) :
    fourVertex (fourPart u) (fourLocal u) = u :=
  four_coordinates_injective (fourPart_vertex _ _) (fourLocal_vertex _ _)

def fourPartDigraph {m : Nat} (H : Digraph (Fin m)) : Digraph (Fin (4 * m)) where
  arc u v := (fourPart u = fourPart v ∧ H.arc (fourLocal u) (fourLocal v)) ∨
    (fourPart v).val = ((fourPart u).val + 1) % 4
  loopless v := by
    rintro (⟨_, hv⟩ | hv)
    · exact H.loopless _ hv
    · have hp := (fourPart v).isLt
      omega

theorem fourPart_cross_arc {m : Nat} (H : Digraph (Fin m)) (u v : Fin (4*m))
    (h : (fourPart v).val = ((fourPart u).val + 1) % 4) :
    (fourPartDigraph H).arc u v := Or.inr h

theorem fourPart_hamiltonian {m : Nat} (H : Digraph (Fin m)) (hm : 0 < m) :
    Hamiltonian (fourPartDigraph H) := by
  refine ⟨by omega, id, fun _ _ h => h, fun v => ⟨v,rfl⟩, ?_⟩
  intro i
  apply Or.inr
  change ((i.val+1) % (4*m)) % 4 = (i.val % 4 + 1) % 4
  rw [Nat.mod_mod_of_dvd _ (by omega : 4 ∣ 4*m)]
  omega

theorem fourPart_surviving {m : Nat} (S : List (Fin (4*m))) (hS : S.Nodup)
    (hsize : S.length < m) (p : Fin 4) :
    ∃ v, v ∉ S ∧ fourPart v = p := by
  classical
  let part := Finset.univ.image (fourVertex (m := m) p)
  have hcard : part.card = m := by
    rw [Finset.card_image_of_injective _ (fourVertex_injective p)]
    simp
  have hlt : S.toFinset.card < part.card := by
    simpa only [hcard, List.toFinset_card_of_nodup hS] using hsize
  obtain ⟨v,hv,hvS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
  exact ⟨fourVertex p w, by simpa using hvS, fourPart_vertex p w⟩

theorem fourPart_kStrong {m : Nat} (H : Digraph (Fin m)) (hm : 0 < m) :
    KStrong (fourPartDigraph H) m := by
  refine ⟨by omega, ?_⟩
  intro S hS hsize
  obtain ⟨v0,hv0,hp0⟩ := fourPart_surviving S hS hsize 0
  obtain ⟨v1,hv1,hp1⟩ := fourPart_surviving S hS hsize 1
  obtain ⟨v2,hv2,hp2⟩ := fourPart_surviving S hS hsize 2
  obtain ⟨v3,hv3,hp3⟩ := fourPart_surviving S hS hsize 3
  have ha01 := fourPart_cross_arc H v0 v1 (by simp [hp0,hp1])
  have ha12 := fourPart_cross_arc H v1 v2 (by simp [hp1,hp2])
  have ha23 := fourPart_cross_arc H v2 v3 (by simp [hp2,hp3])
  have ha30 := fourPart_cross_arc H v3 v0 (by simp [hp3,hp0])
  refine ⟨⟨v0,hv0⟩, ?_⟩
  intro u v hu hv
  have hu0 : Reach (fourPartDigraph H) (fun z => z ∉ S) u v0 := by
    have hup := (fourPart u).isLt
    interval_cases hval : (fourPart u).val
    · have hau1 := fourPart_cross_arc H u v1 (by simp [hp1,hval])
      exact Reach.step (Reach.step (Reach.step (Reach.step (Reach.refl hu)
        hau1 hv1) ha12 hv2) ha23 hv3) ha30 hv0
    · have hau2 := fourPart_cross_arc H u v2 (by simp [hp2,hval])
      exact Reach.step (Reach.step (Reach.step (Reach.refl hu) hau2 hv2)
        ha23 hv3) ha30 hv0
    · have hau3 := fourPart_cross_arc H u v3 (by simp [hp3,hval])
      exact Reach.step (Reach.step (Reach.refl hu) hau3 hv3) ha30 hv0
    · exact Reach.step (Reach.refl hu) (fourPart_cross_arc H u v0 (by simp [hp0,hval])) hv0
  have hu1 := Reach.step hu0 ha01 hv1
  have hu2 := Reach.step hu1 ha12 hv2
  have hu3 := Reach.step hu2 ha23 hv3
  have hvp := (fourPart v).isLt
  interval_cases hval : (fourPart v).val
  · exact Reach.step hu3 (fourPart_cross_arc H v3 v (by simp [hp3,hval])) hv
  · exact Reach.step hu0 (fourPart_cross_arc H v0 v (by simp [hp0,hval])) hv
  · exact Reach.step hu1 (fourPart_cross_arc H v1 v (by simp [hp1,hval])) hv
  · exact Reach.step hu2 (fourPart_cross_arc H v2 v (by simp [hp2,hval])) hv

theorem fourPart_alpha {m a : Nat} (H : Digraph (Fin m)) (ha : AlphaTwoLE H a) :
    AlphaTwoLE (fourPartDigraph H) (4*a) := by
  classical
  intro xs hnodup hind
  have hfiber : ∀ p : Fin 4, (xs.toFinset.filter (fun v => fourPart v = p)).card ≤ a := by
    intro p
    let s := xs.toFinset.filter (fun v => fourPart v = p)
    have hinj : Set.InjOn fourLocal (s : Set (Fin (4*m))) := by
      intro u hu v hv hlocal
      exact four_coordinates_injective
        ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm) hlocal
    have hi : Independent H (fun z => z ∈ (s.image fourLocal).toList) := by
      intro z w hz hw hzw hedge
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hz)
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hw)
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      have huv : u ≠ v := by intro h; exact hzw (congrArg fourLocal h)
      exact hind u v (List.mem_toFinset.mp hu'.1) (List.mem_toFinset.mp hv'.1) huv
        ⟨Or.inl ⟨hu'.2.trans hv'.2.symm,hedge.1⟩,
         Or.inl ⟨hv'.2.trans hu'.2.symm,hedge.2⟩⟩
    have hb := ha (s.image fourLocal).toList (Finset.nodup_toList _) hi
    simpa only [Finset.length_toList, Finset.card_image_iff.mpr hinj] using hb
  have hcard : xs.toFinset.card = ∑ p : Fin 4, (xs.toFinset.filter (fun v => fourPart v = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc
    xs.length = xs.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = ∑ p : Fin 4, (xs.toFinset.filter (fun v => fourPart v = p)).card := hcard
    _ ≤ ∑ _p : Fin 4, a := Finset.sum_le_sum (fun p _ => hfiber p)
    _ = 4*a := by simp

theorem fourPart_triangleFree {m : Nat} (H : Digraph (Fin m))
    (ht : ∀ x y z, H.arc x y → H.arc y z → H.arc z x → False) :
    ∀ x y z, (fourPartDigraph H).arc x y → (fourPartDigraph H).arc y z →
      (fourPartDigraph H).arc z x → False := by
  intro x y z hxy hyz hzx
  have hx := (fourPart x).isLt
  have hy := (fourPart y).isLt
  have hz := (fourPart z).isLt
  have hxyP : (fourPart x).val = (fourPart y).val ∨
      (fourPart y).val = ((fourPart x).val+1)%4 := by
    rcases hxy with ⟨h,_⟩ | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr h
  have hyzP : (fourPart y).val = (fourPart z).val ∨
      (fourPart z).val = ((fourPart y).val+1)%4 := by
    rcases hyz with ⟨h,_⟩ | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr h
  have hzxP : (fourPart z).val = (fourPart x).val ∨
      (fourPart x).val = ((fourPart z).val+1)%4 := by
    rcases hzx with ⟨h,_⟩ | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr h
  have hp : fourPart x = fourPart y ∧ fourPart y = fourPart z := by
    constructor <;> apply Fin.ext <;> omega
  have hexy : H.arc (fourLocal x) (fourLocal y) := by
    rcases hxy with h | h
    · exact h.2
    · have hval := congrArg Fin.val hp.1
      omega
  have heyz : H.arc (fourLocal y) (fourLocal z) := by
    rcases hyz with h | h
    · exact h.2
    · have hval := congrArg Fin.val hp.2
      omega
  have hezx : H.arc (fourLocal z) (fourLocal x) := by
    rcases hzx with h | h
    · exact h.2
    · have hval := congrArg Fin.val (hp.1.trans hp.2)
      omega
  exact ht _ _ _ hexy heyz hezx

theorem fourPart_not_kStrong_succ {m : Nat} (H : Digraph (Fin m)) (hm : 0 < m) :
    ¬ KStrong (fourPartDigraph H) (m+1) := by
  classical
  intro hstrong
  let S := List.ofFn (fourVertex (m := m) 0)
  have hS : S.Nodup := List.nodup_ofFn.mpr (fourVertex_injective 0)
  have hsize : S.length < m+1 := by simp [S]
  have hmem : ∀ v : Fin (4*m), v ∈ S ↔ fourPart v = 0 := by
    intro v
    constructor
    · intro hv
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hv
      rw [← hi]
      exact fourPart_vertex _ _
    · intro hv
      apply List.mem_ofFn.mpr
      refine ⟨fourLocal v, ?_⟩
      rw [← hv]
      exact fourVertex_coordinates v
  let u := fourVertex (m := m) 3 ⟨0,hm⟩
  let v := fourVertex (m := m) 1 ⟨0,hm⟩
  have hu : u ∉ S := by rw [hmem]; simp [u]
  have hv : v ∉ S := by rw [hmem]; simp [v]
  have hnoreach : ¬ Reach (fourPartDigraph H) (fun z => z ∉ S) u v := by
    apply no_reach_across_cut (fourPartDigraph H) (fun z => z ∉ S)
      (fun z => fourPart z = 3) (fun z => z ∉ S ∧ fourPart z ≠ 3)
    · intro z hz
      by_cases hp : fourPart z = 3
      · exact Or.inl hp
      · exact Or.inr ⟨hz,hp⟩
    · intro z hl hr
      exact hr.2 hl
    · intro x y hx hy hxy
      rcases hxy with ⟨hpart,_⟩ | hpart
      · exact hy.2 (hpart.symm.trans hx)
      · have hzero : fourPart y = 0 := by
          apply Fin.ext
          simpa [hx] using hpart
        exact hy.1 ((hmem y).mpr hzero)
    · simp [u]
    · exact ⟨hv,by simp [v]⟩
  exact hnoreach ((hstrong.2 S hS hsize).2 u v hu hv)

theorem fourPart_connectivity {m : Nat} (H : Digraph (Fin m)) (hm : 0 < m) :
    connectivity (fourPartDigraph H) = m :=
  connectivity_eq_of_kStrong_not_succ _ (fourPart_kStrong H hm)
    (fourPart_not_kStrong_succ H hm)

theorem fourPart_not_pancyclic {m : Nat} (H : Digraph (Fin m)) (hm : 0 < m)
    (ht : TriangleFree H) : ¬ Pancyclic (fourPartDigraph H) :=
  triangleFree_not_pancyclic _ (fourPart_triangleFree H ht) (by omega)

/-- The general four-copy cyclic lift used in the paper's final section. -/
theorem fourPart_properties {m a : Nat} (H : Digraph (Fin m)) (hm : 0 < m)
    (ha : AlphaTwoLE H a) (ht : TriangleFree H) :
    Hamiltonian (fourPartDigraph H) ∧ connectivity (fourPartDigraph H) = m ∧
    AlphaTwoLE (fourPartDigraph H) (4*a) ∧ TriangleFree (fourPartDigraph H) ∧
    ¬ Pancyclic (fourPartDigraph H) :=
  ⟨fourPart_hamiltonian H hm, fourPart_connectivity H hm, fourPart_alpha H ha,
    fourPart_triangleFree H ht, fourPart_not_pancyclic H hm ht⟩

end ChvatalErdos

#print axioms ChvatalErdos.fourPart_hamiltonian
#print axioms ChvatalErdos.fourPart_kStrong
#print axioms ChvatalErdos.fourPart_alpha
#print axioms ChvatalErdos.fourPart_triangleFree
#print axioms ChvatalErdos.fourPart_not_kStrong_succ
#print axioms ChvatalErdos.fourPart_properties
