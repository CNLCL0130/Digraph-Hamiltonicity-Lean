import ChvatalErdos.LayerIteration
import ChvatalErdos.LayerClosing

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

theorem halving_rounds_below (p a : Nat) (hp : 1 ≤ p) (hpa : p ≤ a) :
    halfUp^[Nat.clog 2 a] p = 1 := by
  rw [halfUp_iterate p _ hp]
  have ha := Nat.le_pow_clog (by omega : 1 < 2) a
  rw [Nat.div_eq_of_lt (by omega : p-1 < 2^Nat.clog 2 a)]

variable {V : Type} [DecidableEq V] {D : Digraph V} {p a l : Nat}

/-- The full sequence of halving rounds followed by a reserved closing layer.
The coverage identity distinguishes used and unused whole resource paths. -/
theorem cycle_from_layers (F₀ : Fin p → DPath D) (sizes : Fin l → Nat)
    (J : ∀ j, Digraph (Fin (sizes j))) (R : (Σ j : Fin l, Fin (sizes j)) → DPath D)
    (hp0 : 1 ≤ p) (hp : p ≤ a) (hl : Nat.clog 2 a+1 ≤ l)
    (hJ : ∀ j, KStrong (J j) a)
    (hF₀ : ∀ i j, i ≠ j → Disjoint (F₀ i).support (F₀ j).support)
    (hR : ∀ u v, u ≠ v → Disjoint (R u).support (R v).support)
    (hF₀R : ∀ i w, Disjoint (F₀ i).support (R w).support)
    (he : ∀ j u v, (J j).arc u v → D.arc (R ⟨j,u⟩).last (R ⟨j,v⟩).first)
    (hout : ∀ j i, a ≤ (Finset.univ.filter (fun w => D.arc (F₀ i).last (R ⟨j,w⟩).first)).card)
    (hinn : ∀ j i, a ≤ (Finset.univ.filter (fun w => D.arc (R ⟨j,w⟩).last (F₀ i).first)).card) :
    ∃ C : DCycle D, ∃ U : Finset (Σ j : Fin l, Fin (sizes j)),
      (∀ z, z ∈ C.path.support ↔ (∃ i, z ∈ (F₀ i).support) ∨ ∃ w ∈ U, z ∈ (R w).support) ∧
      (∀ u v, (∃ i, (F₀ i).HasArc u v) → C.HasArc u v) ∧
      ∀ w, w ∉ U → Disjoint C.path.support (R w).support := by
  let k := Nat.clog 2 a
  obtain ⟨F,U,hF,hUsed,hcov,harcs,hfirst,hlast⟩ := iterate_layers F₀ sizes J R hp hJ hF₀ hR hF₀R he hout hinn k (by dsimp [k]; omega)
  have hcount : halfUp^[k] p = 1 := halving_rounds_below p a hp0 hp
  let one : Fin (halfUp^[k] p) := ⟨0,by rw [hcount]; omega⟩
  have hall : ∀ i : Fin (halfUp^[k] p), i = one := by
    intro i
    apply Fin.ext
    have hi := i.isLt
    change i.val = 0
    omega
  let P := F one
  have hPcov : ∀ z, z ∈ P.support ↔ (∃ i, z ∈ (F₀ i).support) ∨ ∃ w ∈ U, z ∈ (R w).support := by
    intro z
    rw [← hcov]
    constructor
    · intro hz; exact ⟨one,hz⟩
    · rintro ⟨i,hi⟩; rwa [hall i] at hi
  let j : Fin l := ⟨k,by dsimp [k]; omega⟩
  have hPR : ∀ w, Disjoint P.support (R ⟨j,w⟩).support := by
    intro w
    apply Finset.disjoint_left.mpr
    intro z hz hzR
    rcases (hPcov z).1 hz with ⟨i,hzi⟩ | ⟨v,hv,hzv⟩
    · exact Finset.disjoint_left.mp (hF₀R i ⟨j,w⟩) hzi hzR
    · have hvne : v ≠ ⟨j,w⟩ := by
        intro heq
        have hh := hUsed v hv
        rw [heq] at hh
        change k < k at hh
        omega
      exact Finset.disjoint_left.mp (hR v ⟨j,w⟩ hvne) hzv hzR
  have hRj : ∀ u v, u ≠ v → Disjoint (R ⟨j,u⟩).support (R ⟨j,v⟩).support := by
    intro u v huv
    apply hR
    intro heq
    exact huv (by simpa using heq)
  have houtP : a ≤ (Finset.univ.filter (fun w => D.arc P.last (R ⟨j,w⟩).first)).card := by
    obtain ⟨i,hi⟩ := hlast one
    change a ≤ (Finset.univ.filter (fun w => D.arc (F one).last (R ⟨j,w⟩).first)).card
    rw [hi]
    exact hout j i
  have hinnP : a ≤ (Finset.univ.filter (fun w => D.arc (R ⟨j,w⟩).last P.first)).card := by
    obtain ⟨i,hi⟩ := hfirst one
    change a ≤ (Finset.univ.filter (fun w => D.arc (R ⟨j,w⟩).last (F one).first)).card
    rw [hi]
    exact hinn j i
  obtain ⟨C,Q,hCcov,hCarcs,hwhole⟩ := close_with_layer P (J j) (hJ j) (by omega) (fun w => R ⟨j,w⟩) hRj hPR (he j) houtP hinnP
  let added : Finset (Σ j : Fin l, Fin (sizes j)) := Q.support.image (fun w => ⟨j,w⟩)
  have hadd : ∀ v, v ∈ added ↔ ∃ w ∈ Q.support, Sigma.mk j w = v := by intro v; simp [added]
  have hcover : ∀ z, z ∈ C.path.support ↔ (∃ i, z ∈ (F₀ i).support) ∨ ∃ w ∈ U ∪ added, z ∈ (R w).support := by
    intro z
    rw [hCcov,hPcov]
    constructor
    · rintro ((hz₀ | ⟨v,hv,hzv⟩) | ⟨w,hw,hzw⟩)
      · exact Or.inl hz₀
      · exact Or.inr ⟨v,Finset.mem_union_left _ hv,hzv⟩
      · exact Or.inr ⟨⟨j,w⟩,Finset.mem_union_right _ ((hadd _).2 ⟨w,hw,rfl⟩),hzw⟩
    · rintro (hz₀ | ⟨v,hv,hzv⟩)
      · exact Or.inl (Or.inl hz₀)
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact Or.inl (Or.inr ⟨v,hv,hzv⟩)
        · obtain ⟨w,hw,rfl⟩ := (hadd v).1 hv
          exact Or.inr ⟨w,hw,hzv⟩
  refine ⟨C,U ∪ added,hcover,?_,?_⟩
  · intro u v huv
    obtain ⟨i,hi⟩ := harcs u v huv
    apply hCarcs u v
    rwa [hall i] at hi
  · intro w hw
    apply Finset.disjoint_left.mpr
    intro z hz hzR
    rcases (hcover z).1 hz with ⟨i,hzi⟩ | ⟨v,hv,hzv⟩
    · exact Finset.disjoint_left.mp (hF₀R i w) hzi hzR
    · have hvw : v ≠ w := fun heq => hw (heq ▸ hv)
      exact Finset.disjoint_left.mp (hR v w hvw) hzv hzR

end ChvatalErdos

#print axioms ChvatalErdos.cycle_from_layers
