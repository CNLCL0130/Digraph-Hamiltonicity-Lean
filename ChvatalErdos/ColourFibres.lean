import ChvatalErdos.Connectivity
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.ColourFibres
variable {m l : Nat}

noncomputable def fibre (colour : Fin m → Fin l) (j : Fin l) : Finset (Fin m) :=
  Finset.univ.filter (fun i => colour i = j)

noncomputable def size (colour : Fin m → Fin l) (j : Fin l) : Nat := (fibre colour j).card

noncomputable def enumeration (colour : Fin m → Fin l) (j : Fin l) :
    Fin (size colour j) ≃ fibre colour j := by
  simpa only [Fintype.card_coe] using (Fintype.equivFin (fibre colour j)).symm

noncomputable def index (colour : Fin m → Fin l) (w : Σ j : Fin l, Fin (size colour j)) : Fin m :=
  (enumeration colour w.1 w.2).val

theorem index_colour (colour : Fin m → Fin l) (w : Σ j : Fin l, Fin (size colour j)) :
    colour (index colour w) = w.1 :=
  (Finset.mem_filter.mp (enumeration colour w.1 w.2).property).2

theorem index_injective (colour : Fin m → Fin l) : Function.Injective (index colour) := by
  intro u v huv
  have hcol : u.1 = v.1 := (index_colour colour u).symm.trans ((congrArg colour huv).trans (index_colour colour v))
  cases u with | mk j u =>
    cases v with | mk k v =>
      dsimp at hcol
      subst k
      have he : enumeration colour j u = enumeration colour j v := Subtype.ext huv
      have huv' := (enumeration colour j).injective he
      subst v
      rfl

theorem index_surjective (colour : Fin m → Fin l) : Function.Surjective (index colour) := by
  intro i
  let v : fibre colour (colour i) := ⟨i,by simp [fibre]⟩
  refine ⟨⟨colour i,(enumeration colour (colour i)).symm v⟩,?_⟩
  simp [index,v]

theorem fibre_index_injective (colour : Fin m → Fin l) (j : Fin l) :
    Function.Injective (fun i : Fin (size colour j) => index colour ⟨j,i⟩) := by
  intro i k hik
  have hh := index_injective colour hik
  simpa using hh

theorem fibre_index_mem (colour : Fin m → Fin l) (j : Fin l) (i : Fin (size colour j)) :
    index colour ⟨j,i⟩ ∈ fibre colour j := (enumeration colour j i).property

theorem fibre_index_surjective (colour : Fin m → Fin l) (j : Fin l) (i : Fin m)
    (hi : i ∈ fibre colour j) : ∃ k, index colour ⟨j,k⟩ = i := by
  let v : fibre colour j := ⟨i,hi⟩
  exact ⟨(enumeration colour j).symm v,by simp [index,v]⟩

theorem filter_card (colour : Fin m → Fin l) (j : Fin l) (P : Fin m → Prop) :
    (Finset.univ.filter (fun i : Fin (size colour j) => P (index colour ⟨j,i⟩))).card =
      ((fibre colour j).filter P).card := by
  apply Finset.card_bij (fun i _ => index colour ⟨j,i⟩)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨fibre_index_mem colour j i,(Finset.mem_filter.mp hi).2⟩
  · intro i _ k _ hik
    exact fibre_index_injective colour j hik
  · intro v hv
    obtain ⟨i,hi⟩ := fibre_index_surjective colour j v (Finset.mem_filter.mp hv).1
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi ▸ (Finset.mem_filter.mp hv).2⟩,hi⟩

theorem induced_strong (colour : Fin m → Fin l) (j : Fin l) (J : Digraph (Fin m)) (a : Nat)
    (hJ : KStrongOn J (fibre colour j) a) :
    KStrong (inducedDigraph J (fun i : Fin (size colour j) => index colour ⟨j,i⟩)) a :=
  kStrongOn_induced J (fibre colour j) hJ _ (fibre_index_injective colour j)
    (fibre_index_mem colour j) (fibre_index_surjective colour j) rfl

end ChvatalErdos.ColourFibres

#print axioms ChvatalErdos.ColourFibres.index_injective
#print axioms ChvatalErdos.ColourFibres.induced_strong
