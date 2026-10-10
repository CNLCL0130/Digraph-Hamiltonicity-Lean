import ChvatalErdos.Paths
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace ChvatalErdos
namespace Forest

variable {V : Type} [DecidableEq V] {D : Digraph V}
noncomputable local instance : DecidableEq (UPath D) := Classical.typeDecidableEq _

def Valid (F : Finset (UPath D)) : Prop :=
  ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P.support Q.support

def Covers (F : Finset (UPath D)) (v : V) : Prop := ∃ P ∈ F, v ∈ P.support
def IsEnd (F : Finset (UPath D)) (v : V) : Prop := ∃ P ∈ F, v = P.first ∨ v = P.last
def HasEdge (F : Finset (UPath D)) (u v : V) : Prop := ∃ P ∈ F, P.HasEdge u v

def Extends (F G : Finset (UPath D)) : Prop :=
  (∀ v, Covers G v ↔ Covers F v) ∧
  (∀ u v, HasEdge F u v → HasEdge G u v) ∧
  (∀ v, IsEnd G v → IsEnd F v)

theorem extends_refl (F : Finset (UPath D)) : Extends F F :=
  ⟨fun _ => Iff.rfl,fun _ _ h => h,fun _ h => h⟩

theorem extends_trans {F G H : Finset (UPath D)} (hFG : Extends F G) (hGH : Extends G H) :
    Extends F H := ⟨fun v => (hGH.1 v).trans (hFG.1 v),
      fun u v h => hGH.2.1 u v (hFG.2.1 u v h),fun v h => hFG.2.2 v (hGH.2.2 v h)⟩

theorem merge {F : Finset (UPath D)} (hF : Valid F) (P Q : UPath D)
    (hP : P ∈ F) (hQ : Q ∈ F) (hne : P ≠ Q) (he : TwoCycle D P.first Q.first) :
    ∃ G : Finset (UPath D), Valid G ∧ Extends F G ∧ G.card < F.card := by
  classical
  have hd : Disjoint P.reverse.support Q.support := by
    rw [UPath.support_reverse]
    exact hF P hP Q hQ hne
  have he' : TwoCycle D P.reverse.last Q.first := by rwa [UPath.last_reverse]
  let R := P.reverse.join Q hd he'
  let T := (F.erase P).erase Q
  let G := insert R T
  have hRsupport : R.support = P.support ∪ Q.support := by
    simp only [R,UPath.support_join,UPath.support_reverse]
  have hT : ∀ A ∈ T, A ∈ F ∧ A ≠ P ∧ A ≠ Q := by
    intro A hA
    simp only [T,Finset.mem_erase] at hA
    exact ⟨hA.2.2,hA.2.1,hA.1⟩
  have hremain : ∀ A ∈ F, A ≠ P → A ≠ Q → A ∈ T := by
    intro A hA hAP hAQ
    simp [T,hA,hAP,hAQ]
  have hRT : ∀ A ∈ T, Disjoint R.support A.support := by
    intro A hA
    obtain ⟨hAF,hAP,hAQ⟩ := hT A hA
    rw [hRsupport,Finset.disjoint_union_left]
    exact ⟨hF P hP A hAF hAP.symm,hF Q hQ A hAF hAQ.symm⟩
  have hvalid : Valid G := by
    intro A hA B hB hAB
    rcases Finset.mem_insert.mp hA with rfl | hA <;>
      rcases Finset.mem_insert.mp hB with rfl | hB
    · exact (hAB rfl).elim
    · exact hRT B hB
    · exact (hRT A hA).symm
    · exact hF A (hT A hA).1 B (hT B hB).1 hAB
  have hcover : ∀ v, Covers G v ↔ Covers F v := by
    intro v
    constructor
    · rintro ⟨A,hA,hv⟩
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rw [hRsupport] at hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact ⟨P,hP,hv⟩
        · exact ⟨Q,hQ,hv⟩
      · exact ⟨A,(hT A hA).1,hv⟩
    · rintro ⟨A,hA,hv⟩
      by_cases hAP : A = P
      · subst A
        exact ⟨R,Finset.mem_insert_self _ _,by rw [hRsupport]; exact Finset.mem_union_left _ hv⟩
      by_cases hAQ : A = Q
      · subst A
        exact ⟨R,Finset.mem_insert_self _ _,by rw [hRsupport]; exact Finset.mem_union_right _ hv⟩
      exact ⟨A,Finset.mem_insert_of_mem (hremain A hA hAP hAQ),hv⟩
  have hedge : ∀ u v, HasEdge F u v → HasEdge G u v := by
    rintro u v ⟨A,hA,huv⟩
    by_cases hAP : A = P
    · subst A
      exact ⟨R,Finset.mem_insert_self _ _,UPath.edge_join_left _ _ _ _ u v (P.edge_reverse u v huv)⟩
    by_cases hAQ : A = Q
    · subst A
      exact ⟨R,Finset.mem_insert_self _ _,UPath.edge_join_right _ _ _ _ u v huv⟩
    exact ⟨A,Finset.mem_insert_of_mem (hremain A hA hAP hAQ),huv⟩
  have hend : ∀ v, IsEnd G v → IsEnd F v := by
    rintro v ⟨A,hA,hv⟩
    rcases Finset.mem_insert.mp hA with rfl | hA
    · rcases hv with hv | hv
      · exact ⟨P,hP,Or.inr (by simpa [R,UPath.first_join,UPath.first_reverse] using hv)⟩
      · exact ⟨Q,hQ,Or.inr (by simpa [R,UPath.last_join] using hv)⟩
    · exact ⟨A,(hT A hA).1,hv⟩
  refine ⟨G,hvalid,⟨hcover,hedge,hend⟩,?_⟩
  have hQerase : Q ∈ F.erase P := Finset.mem_erase.mpr ⟨hne.symm,hQ⟩
  have hsize := Finset.card_insert_le R T
  have hp := Finset.card_erase_of_mem hP
  have hq := Finset.card_erase_of_mem hQerase
  have hpPos := Finset.card_pos.mpr ⟨P,hP⟩
  have hqPos := Finset.card_pos.mpr ⟨Q,hQerase⟩
  dsimp [G,T]
  dsimp [T] at hsize
  omega

theorem extension {F : Finset (UPath D)} (hF : Valid F) (a : Nat) (ha : AlphaTwoLE D a) :
    ∃ G : Finset (UPath D), Valid G ∧ Extends F G ∧ G.card ≤ a := by
  classical
  have hex : ∃ k : Nat, ∃ G : Finset (UPath D), Valid G ∧ Extends F G ∧ G.card = k :=
    ⟨F.card,F,hF,extends_refl F,rfl⟩
  obtain ⟨G,hG,hFG,hcard⟩ := Nat.find_spec hex
  have hmin : ∀ H : Finset (UPath D), Valid H → Extends F H → G.card ≤ H.card := by
    intro H hH hFH
    rw [hcard]
    exact Nat.find_min' hex ⟨H,hH,hFH,rfl⟩
  have hnonadj : ∀ P ∈ G, ∀ Q ∈ G, P ≠ Q → ¬TwoCycle D P.first Q.first := by
    intro P hP Q hQ hne he
    obtain ⟨H,hH,hGH,hlt⟩ := merge hG P Q hP hQ hne he
    exact (Nat.not_lt_of_ge (hmin H hH (extends_trans hFG hGH))) hlt
  let heads := G.image UPath.first
  have hinj : Set.InjOn UPath.first (↑G : Set (UPath D)) := by
    intro P hP Q hQ heq
    by_contra hne
    exact Finset.disjoint_left.mp (hG P hP Q hQ hne) P.first_mem (heq ▸ Q.first_mem)
  have hheads : heads.card = G.card := Finset.card_image_iff.mpr hinj
  have hind : Independent D (fun v => v ∈ heads) := by
    intro u v hu hv huv htwo
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hv
    have hpq : P ≠ Q := fun h => huv (congrArg UPath.first h)
    exact hnonadj P hP Q hQ hpq htwo
  have hbound := ha heads.toList (Finset.nodup_toList _)
    (by simpa only [Finset.mem_toList] using hind)
  refine ⟨G,hG,hFG,?_⟩
  simpa only [Finset.length_toList,hheads] using hbound

def singletonPath (v : V) : UPath D where
  vertices := [v]
  nonempty := by simp
  nodup := by simp
  chain := by simp

theorem path_cover (U : Finset V) (a : Nat) (ha : AlphaTwoLE D a) :
    ∃ G : Finset (UPath D), Valid G ∧ G.card ≤ a ∧ ∀ v, Covers G v ↔ v ∈ U := by
  classical
  let F := U.image (singletonPath (D := D))
  have hF : Valid F := by
    intro P hP Q hQ hpq
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hQ
    have huv : u ≠ v := fun h => hpq (congrArg singletonPath h)
    simpa [singletonPath,UPath.support] using huv.symm
  obtain ⟨G,hG,hFG,hsize⟩ := extension hF a ha
  refine ⟨G,hG,hsize,?_⟩
  intro v
  rw [hFG.1 v]
  constructor
  · rintro ⟨P,hP,hv⟩
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hP
    have hvu : v = u := by simpa [singletonPath,UPath.support] using hv
    exact hvu ▸ hu
  · intro hv
    refine ⟨singletonPath v,Finset.mem_image_of_mem _ hv,?_⟩
    simp [singletonPath,UPath.support]

noncomputable def ends (G : Finset (UPath D)) : Finset V :=
  G.biUnion (fun P => {P.first,P.last})

theorem ends_card_le (G : Finset (UPath D)) : (ends G).card ≤ 2 * G.card := by
  classical
  apply (Finset.card_biUnion_le).trans
  have h : (∑ P ∈ G, ({P.first,P.last} : Finset V).card) ≤ ∑ _P ∈ G, 2 :=
    Finset.sum_le_sum (fun P _ => Finset.card_le_two)
  simpa [Nat.mul_comm] using h

theorem mem_ends (G : Finset (UPath D)) (v : V) : v ∈ ends G ↔ IsEnd G v := by
  simp [ends,IsEnd]

end Forest
end ChvatalErdos

#print axioms ChvatalErdos.Forest.merge
#print axioms ChvatalErdos.Forest.extension
#print axioms ChvatalErdos.Forest.path_cover
#print axioms ChvatalErdos.Forest.ends_card_le


