import ChvatalErdos.BipartiteExample

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos

def unbalancedColour (a : Nat) (v : Fin (2*a-1)) : Bool := decide (v.val < a)

theorem unbalanced_left_card (a : Nat) (ha : 2 ≤ a) : (colourPart (unbalancedColour a) true).card = a := by
  have hh : (Finset.univ : Finset (Fin a)).card = (colourPart (unbalancedColour a) true).card := by
    apply Finset.card_bij (fun v _ => (⟨v.val,by have h := v.isLt; omega⟩ : Fin (2*a-1)))
    · intro v hv
      simp only [colourPart,Finset.mem_filter,Finset.mem_univ,true_and,unbalancedColour,decide_eq_true_eq]
      exact v.isLt
    · intro v _ w _ he
      apply Fin.ext
      exact congrArg (fun z : Fin (2*a-1) => z.val) he
    · intro v hv
      have hv' : v.val < a := by simpa only [colourPart,Finset.mem_filter,Finset.mem_univ,true_and,unbalancedColour,decide_eq_true_eq] using hv
      exact ⟨⟨v.val,hv'⟩,Finset.mem_univ _,Fin.ext rfl⟩
  simpa using hh.symm

theorem unbalanced_right_card (a : Nat) (ha : 2 ≤ a) : (colourPart (unbalancedColour a) false).card = a-1 := by
  have hh : (Finset.univ : Finset (Fin (a-1))).card = (colourPart (unbalancedColour a) false).card := by
    apply Finset.card_bij (fun v _ => (⟨a+v.val,by have h := v.isLt; omega⟩ : Fin (2*a-1)))
    · intro v hv
      simp only [colourPart,Finset.mem_filter,Finset.mem_univ,true_and,unbalancedColour,decide_eq_false_iff_not]
      change ¬a+v.val < a
      omega
    · intro v _ w _ he
      have hh := congrArg Fin.val he
      change a+v.val = a+w.val at hh
      apply Fin.ext
      omega
    · intro v hv
      have hv' : ¬v.val < a := by simpa only [colourPart,Finset.mem_filter,Finset.mem_univ,true_and,unbalancedColour,decide_eq_false_iff_not] using hv
      refine ⟨⟨v.val-a,by have h := v.isLt; omega⟩,Finset.mem_univ _,?_⟩
      apply Fin.ext
      change a+(v.val-a) = v.val
      omega
  simpa using hh.symm

theorem unbalanced_counterexample (a : Nat) (ha : 2 ≤ a) :
    ∃ D : Digraph (Fin (2*a-1)), AlphaTwoLE D a ∧ KStrong D (a-1) ∧ ¬Hamiltonian D := by
  refine ⟨completeBipartite (unbalancedColour a),?_,?_,?_⟩
  · apply completeBipartite_alpha
    intro c
    cases c
    · rw [unbalanced_right_card a ha]; omega
    · rw [unbalanced_left_card a ha]
  · apply completeBipartite_strong _ _ (by omega)
    intro c
    cases c
    · rw [unbalanced_right_card a ha]
    · rw [unbalanced_left_card a ha]; omega
  · exact completeBipartite_no_odd_hamiltonian _ (by omega)

theorem f₂_linear_lower (a : Nat) (ha : 2 ≤ a) : a ≤ f₂ a := by
  by_contra h
  have hle : f₂ a ≤ a-1 := by omega
  obtain ⟨D,hα,hstrong,hnot⟩ := unbalanced_counterexample a ha
  have hstrong' : KStrong D (f₂ a) := by
    refine ⟨by have hh := hstrong.1; omega,?_⟩
    intro S hS hsize
    exact hstrong.2 S hS (hsize.trans_le hle)
  exact hnot ((f₂_sufficient a).2 (2*a-1) D hα hstrong')

end ChvatalErdos

#print axioms ChvatalErdos.unbalanced_counterexample
#print axioms ChvatalErdos.f₂_linear_lower
