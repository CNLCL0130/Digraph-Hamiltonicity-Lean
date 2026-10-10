import ChvatalErdos.InducedCore

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
variable {n c m b : Nat}

theorem induce_cycle_family (D : Digraph (Fin n)) (e : Fin c → Fin n) (he : Function.Injective e)
    (Q : Fin m → UCycle D b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hinside : ∀ i t, ∃ v, e v = (Q i).vertex t)
    (hcover : ∀ v, ∃ i t, (Q i).vertex t = e v) :
    ∃ P : Fin m → UCycle (inducedDigraph D e) b,
      (∀ i k, i ≠ k → Disjoint (P i).support (P k).support) ∧
      ∀ v, ∃ i t, (P i).vertex t = v := by
  choose vertex hvertex using hinside
  let P : Fin m → UCycle (inducedDigraph D e) b := fun i => {
    vertex := vertex i
    injective := by
      intro t s hts
      apply (Q i).injective
      rw [← hvertex i t,← hvertex i s,hts]
    edge := by
      intro t
      change TwoCycle D (e (vertex i t)) (e (vertex i (cyclicSucc t)))
      rw [hvertex,hvertex]
      exact (Q i).edge t }
  refine ⟨P,?_,?_⟩
  · intro i k hik
    apply Finset.disjoint_left.mpr
    intro z hzi hzk
    obtain ⟨t,ht⟩ := (P i).mem_support z |>.1 hzi
    obtain ⟨s,hs⟩ := (P k).mem_support z |>.1 hzk
    have ht' : (Q i).vertex t = e z := by rw [← hvertex i t]; exact congrArg e ht
    have hs' : (Q k).vertex s = e z := by rw [← hvertex k s]; exact congrArg e hs
    exact Finset.disjoint_left.mp (hdis i k hik) ((Q i).mem_support _ |>.2 ⟨t,ht'⟩) ((Q k).mem_support _ |>.2 ⟨s,hs'⟩)
  · intro v
    obtain ⟨i,t,ht⟩ := hcover v
    refine ⟨i,t,he ?_⟩
    exact (hvertex i t).trans ht

theorem packing_core (D : Digraph (Fin n)) (P : Finset (UCycle D b)) (hP : CyclePacking.Valid P) :
    ∃ e : Fin (CyclePacking.covered P).card → Fin n,
      Function.Injective e ∧
      (∀ v, e v ∉ CyclePacking.remainder P) ∧
      (∀ v, v ∉ CyclePacking.remainder P → ∃ w, e w = v) ∧
      (CyclePacking.covered P).card = (Finset.univ \ CyclePacking.remainder P).card ∧
      ∃ Q : Fin P.card → UCycle (inducedDigraph D e) b,
        (∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support) ∧
        ∀ z, ∃ i t, (Q i).vertex t = z := by
  let U := CyclePacking.covered P
  let enumU : Fin U.card ≃ U := by simpa only [Fintype.card_coe] using (Fintype.equivFin U).symm
  let e := fun v => (enumU v).val
  have he : Function.Injective e := by
    intro v w hvw
    exact enumU.injective (Subtype.ext hvw)
  have heU : ∀ v, e v ∈ U := fun v => (enumU v).property
  have hsurj : ∀ v ∈ U, ∃ w, e w = v := by
    intro v hv
    obtain ⟨w,hw⟩ := enumU.surjective ⟨v,hv⟩
    exact ⟨w,congrArg Subtype.val hw⟩
  let enumP : Fin P.card ≃ P := by simpa only [Fintype.card_coe] using (Fintype.equivFin P).symm
  let Q := fun i => (enumP i).val
  have hQ : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support := by
    intro i k hik
    apply hP _ (enumP i).property _ (enumP k).property
    exact fun heq => hik (enumP.injective (Subtype.ext heq))
  refine ⟨e,he,?_,?_,?_,?_⟩
  · intro v hv
    exact (CyclePacking.mem_remainder P _).1 hv (heU v)
  · intro v hv
    apply hsurj v
    simpa [CyclePacking.mem_remainder] using hv
  · congr 1
    ext v
    simp [CyclePacking.remainder]
  · apply induce_cycle_family D e he Q hQ
    · intro i t
      exact hsurj _ ((CyclePacking.mem_covered P _).2 ⟨Q i,(enumP i).property,(Q i).mem_support _ |>.2 ⟨t,rfl⟩⟩)
    · intro v
      obtain ⟨C,hC,hvC⟩ := (CyclePacking.mem_covered P (e v)).1 (heU v)
      obtain ⟨t,ht⟩ := (C.mem_support _).1 hvC
      obtain ⟨i,hi⟩ := enumP.surjective ⟨C,hC⟩
      exact ⟨i,t,by change (enumP i).val.vertex t = e v; rw [hi]; exact ht⟩

end ChvatalErdos

#print axioms ChvatalErdos.packing_core
