import ChvatalErdos.Budgets

set_option autoImplicit false

namespace ChvatalErdos.HalfIndices

def left (p : Nat) (i : Fin (p/2)) : Fin p := ⟨i.val,by have := i.isLt; omega⟩
def right (p : Nat) (i : Fin (p/2)) : Fin p := ⟨p/2+i.val,by have := i.isLt; omega⟩
def extra (p : Nat) (i : Fin (p%2)) : Fin p := ⟨2*(p/2)+i.val,by have := i.isLt; omega⟩

theorem left_injective (p : Nat) : Function.Injective (left p) := by
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin p => q.val) h)

theorem right_injective (p : Nat) : Function.Injective (right p) := by
  intro i j h
  have he := congrArg Fin.val h
  apply Fin.ext
  dsimp [right] at he
  omega

theorem extra_injective (p : Nat) : Function.Injective (extra p) := by
  intro i j h
  have he := congrArg Fin.val h
  apply Fin.ext
  dsimp [extra] at he
  omega

theorem left_ne_right (p : Nat) (i j : Fin (p/2)) : left p i ≠ right p j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [left,right] at hv
  have := i.isLt
  omega

theorem left_ne_extra (p : Nat) (i : Fin (p/2)) (j : Fin (p%2)) : left p i ≠ extra p j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [left,extra] at hv
  have := i.isLt
  omega

theorem right_ne_extra (p : Nat) (i : Fin (p/2)) (j : Fin (p%2)) : right p i ≠ extra p j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [right,extra] at hv
  have := i.isLt
  omega

theorem partition (p : Nat) (i : Fin p) :
    (∃ j, left p j = i) ∨ (∃ j, right p j = i) ∨ (∃ j, extra p j = i) := by
  by_cases hleft : i.val < p/2
  · exact Or.inl ⟨⟨i.val,hleft⟩,Fin.ext rfl⟩
  by_cases hright : i.val < 2*(p/2)
  · refine Or.inr (Or.inl ⟨⟨i.val-p/2,by omega⟩,?_⟩)
    apply Fin.ext
    dsimp [right]
    omega
  · refine Or.inr (Or.inr ⟨⟨i.val-2*(p/2),by have := i.isLt; omega⟩,?_⟩)
    apply Fin.ext
    dsimp [extra]
    omega

theorem output_size (p : Nat) : p/2+p%2 = halfUp p := by unfold halfUp; omega

end ChvatalErdos.HalfIndices

#print axioms ChvatalErdos.HalfIndices.partition
