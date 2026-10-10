import ChvatalErdos.Core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace ChvatalErdos
attribute [local instance] Classical.propDecidable

variable {n K : Nat}

noncomputable def outNeighbours (D : Digraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => D.arc v w)

noncomputable def inNeighbours (D : Digraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => D.arc w v)

theorem kStrong_outdegree (D : Digraph (Fin n)) (hD : KStrong D K) (v : Fin n) :
    K ≤ (outNeighbours D v).card := by
  classical
  by_contra hlt
  let S := outNeighbours D v
  have hS : S.card < K := Nat.lt_of_not_ge hlt
  have hvS : v ∉ S := by simp [S,outNeighbours,D.loopless]
  have hcard : (insert v S).card < n := by
    rw [Finset.card_insert_of_notMem hvS]
    have hn := hD.1
    omega
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (insert v S).card < (Finset.univ : Finset (Fin n)).card by simpa using hcard)
  have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self v S)
  have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
  obtain ⟨x,y,hx,hy,hxy⟩ := kStrong_cut_has_arc D hD S.toList (Finset.nodup_toList _)
    (by simpa using hS) (fun x => x = v) (fun y => y ≠ v ∧ y ∉ S)
    (by intro z hz; by_cases h : z = v
        · exact Or.inl h
        · exact Or.inr ⟨h, by simpa using hz⟩)
    (fun x hx h => h.1 hx) ⟨v,by simpa using hvS,rfl⟩ ⟨w,by simpa using hwS,hwv,hwS⟩
  subst x
  exact hy.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩)

def reverseDigraph (D : Digraph (Fin n)) : Digraph (Fin n) where
  arc u v := D.arc v u
  loopless := D.loopless

theorem reverse_reach (D : Digraph (Fin n)) (allowed : Fin n → Prop) {u v : Fin n}
    (h : Reach D allowed u v) : Reach (reverseDigraph D) allowed v u := by
  induction h with
  | refl hu => exact Reach.refl hu
  | @step v w hp hvw hw ih =>
    have hfirst : Reach (reverseDigraph D) allowed w v :=
      Reach.step (Reach.refl hw) hvw (reach_end D allowed hp)
    exact reach_trans _ _ hfirst ih

theorem kStrong_reverse (D : Digraph (Fin n)) (hD : KStrong D K) :
    KStrong (reverseDigraph D) K := by
  refine ⟨hD.1,?_⟩
  intro S hS hsize
  have hs := hD.2 S hS hsize
  refine ⟨hs.1,?_⟩
  intro u v hu hv
  exact reverse_reach D _ (hs.2 v u hv hu)

theorem kStrong_indegree (D : Digraph (Fin n)) (hD : KStrong D K) (v : Fin n) :
    K ≤ (inNeighbours D v).card :=
  kStrong_outdegree (reverseDigraph D) (kStrong_reverse D hD) v

theorem kStrong_outside_outdegree {r : Nat} (D : Digraph (Fin n)) (hD : KStrong D (K + r))
    (R : Finset (Fin n)) (hR : R.card ≤ r) (v : Fin n) :
    K ≤ (outNeighbours D v \ R).card := by
  have hdegree := kStrong_outdegree D hD v
  have hrem := Finset.card_le_card_sdiff_add_card (s := outNeighbours D v) (t := R)
  omega

theorem kStrong_outside_indegree {r : Nat} (D : Digraph (Fin n)) (hD : KStrong D (K + r))
    (R : Finset (Fin n)) (hR : R.card ≤ r) (v : Fin n) :
    K ≤ (inNeighbours D v \ R).card := by
  have hdegree := kStrong_indegree D hD v
  have hrem := Finset.card_le_card_sdiff_add_card (s := inNeighbours D v) (t := R)
  omega

def KStrongOn (D : Digraph (Fin n)) (U : Finset (Fin n)) (K : Nat) : Prop :=
  K + 1 ≤ U.card ∧ ∀ S : Finset (Fin n), S.card < K →
    StrongOn D (fun v => v ∈ U ∧ v ∉ S)

theorem kStrong_delete {r : Nat} (D : Digraph (Fin n)) (hD : KStrong D (K + r))
    (R : Finset (Fin n)) (hR : R.card ≤ r) :
    KStrongOn D (Finset.univ \ R) K := by
  constructor
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hn := hD.1
    omega
  · intro S hS
    have hsize : (R ∪ S).card < K + r := by
      have h := Finset.card_union_le R S
      omega
    have h := hD.2 (R ∪ S).toList (Finset.nodup_toList _) (by simpa using hsize)
    have heq : (fun v => v ∉ (R ∪ S).toList) = (fun v => v ∈ Finset.univ \ R ∧ v ∉ S) := by
      funext v
      simp
    rw [heq] at h
    exact h

def inducedDigraph {m : Nat} (D : Digraph (Fin n)) (e : Fin m → Fin n) : Digraph (Fin m) where
  arc u v := D.arc (e u) (e v)
  loopless v := D.loopless (e v)

theorem reach_induced {m : Nat} (D : Digraph (Fin n)) (e : Fin m → Fin n)
    (he : Function.Injective e) (U : Fin n → Prop)
    (hsurj : ∀ v, U v → ∃ w, e w = v) (S : Finset (Fin m))
    {u v : Fin m} (h : Reach D (fun x => U x ∧ x ∉ S.image e) (e u) (e v)) :
    Reach (inducedDigraph D e) (fun x => x ∉ S) u v := by
  have hgeneral : ∀ x y, Reach D (fun x => U x ∧ x ∉ S.image e) x y →
      ∀ u v, e u = x → e v = y → Reach (inducedDigraph D e) (fun x => x ∉ S) u v := by
    intro x y hxy
    induction hxy with
    | refl hx =>
      intro u v hu hv
      have huv : u = v := he (hu.trans hv.symm)
      subst v
      apply Reach.refl
      intro huS
      exact hx.2 (hu ▸ Finset.mem_image_of_mem e huS)
    | @step y z hp hyz hz ih =>
      intro u v hu hv
      obtain ⟨w,hw⟩ := hsurj y (reach_end D _ hp).1
      have hp' := ih u w hu hw
      have hlast : (inducedDigraph D e).arc w v := by
        change D.arc (e w) (e v)
        rwa [hw,hv]
      apply Reach.step hp' hlast
      intro hvS
      exact hz.2 (hv ▸ Finset.mem_image_of_mem e hvS)
  exact hgeneral _ _ h u v rfl rfl

theorem kStrongOn_induced {m : Nat} (D : Digraph (Fin n)) (U : Finset (Fin n))
    (hU : KStrongOn D U K) (e : Fin m → Fin n) (he : Function.Injective e)
    (heU : ∀ u, e u ∈ U) (hsurj : ∀ v ∈ U, ∃ u, e u = v) (hm : m = U.card) :
    KStrong (inducedDigraph D e) K := by
  refine ⟨by have hcard := hU.1; omega,?_⟩
  intro S hS hsize
  let T := S.toFinset
  have hT : T.card < K := by simpa [T,List.toFinset_card_of_nodup hS] using hsize
  have hTe : (T.image e).card < K := by rwa [Finset.card_image_of_injective _ he]
  have hconn := hU.2 (T.image e) hTe
  obtain ⟨v,hvU,hvT⟩ := hconn.1
  obtain ⟨u,rfl⟩ := hsurj v hvU
  have huT : u ∉ T := fun hu => hvT (Finset.mem_image_of_mem e hu)
  refine ⟨⟨u,by simpa [T] using huT⟩,?_⟩
  intro x y hx hy
  have hxT : e x ∉ T.image e := by
    simp only [Finset.mem_image]
    rintro ⟨z,hz,hzx⟩
    have hzx' := he hzx
    subst z
    exact hx (by simpa [T] using hz)
  have hyT : e y ∉ T.image e := by
    simp only [Finset.mem_image]
    rintro ⟨z,hz,hzy⟩
    have hzy' := he hzy
    subst z
    exact hy (by simpa [T] using hz)
  have hreach := reach_induced D e he (fun v => v ∈ U) hsurj T
    (hconn.2 (e x) (e y) ⟨heU x,hxT⟩ ⟨heU y,hyT⟩)
  simpa [T] using hreach

end ChvatalErdos

#print axioms ChvatalErdos.kStrong_outdegree
#print axioms ChvatalErdos.kStrong_outside_indegree
#print axioms ChvatalErdos.kStrong_delete
#print axioms ChvatalErdos.kStrongOn_induced
