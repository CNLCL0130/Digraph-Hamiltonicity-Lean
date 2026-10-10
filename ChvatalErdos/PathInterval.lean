import ChvatalErdos.PathPositions
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace ChvatalErdos.UPath
variable {n : Nat} {D : Digraph (Fin n)}

theorem point_last (P : UPath D) : P.point ⟨P.vertices.length-1,by have h := P.length_pos; omega⟩ = P.last := by
  simp [point,last,List.getLast_eq_getElem]

def interval (P : UPath D) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < P.vertices.length) : UPath D where
  vertices := List.ofFn (fun j : Fin (hi-lo+1) => P.point ⟨lo+j.val,by have h := j.isLt; omega⟩)
  nonempty := by intro h; have he := congrArg List.length h; simp at he
  nodup := List.nodup_ofFn.mpr (by
    intro i j hij
    have he := congrArg (fun q : Fin P.vertices.length => q.val) (P.point_injective hij)
    change lo+i.val = lo+j.val at he
    apply Fin.ext
    omega)
  chain := by
    apply List.isChain_iff_getElem.mpr
    intro j hj
    have hj' : j+1 < hi-lo+1 := by simpa using hj
    simpa only [List.getElem_ofFn,Nat.add_assoc] using P.point_step (lo+j) (by omega)

theorem interval_first (P : UPath D) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < P.vertices.length) :
    (P.interval lo hi hle hhi).first = P.point ⟨lo,by omega⟩ := by simp [interval,first]

theorem interval_last (P : UPath D) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < P.vertices.length) :
    (P.interval lo hi hle hhi).last = P.point ⟨hi,hhi⟩ := by
  simp only [interval,last,List.getLast_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

theorem interval_length (P : UPath D) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < P.vertices.length) :
    (P.interval lo hi hle hhi).vertices.length = hi-lo+1 := by simp [interval]

theorem mem_interval (P : UPath D) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < P.vertices.length) (z : Fin n) :
    z ∈ (P.interval lo hi hle hhi).support ↔ ∃ j : Fin P.vertices.length, lo ≤ j.val ∧ j.val ≤ hi ∧ P.point j = z := by
  rw [mem_support]
  change z ∈ List.ofFn (fun j : Fin (hi-lo+1) => P.point ⟨lo+j.val,by have h := j.isLt; omega⟩) ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨⟨lo+j.val,by have h := j.isLt; omega⟩,?_,?_,hj⟩
    · change lo ≤ lo+j.val; omega
    · change lo+j.val ≤ hi; have h := j.isLt; omega
  · rintro ⟨j,hlo,hjhi,hj⟩
    refine ⟨⟨j.val-lo,by omega⟩,?_⟩
    have he : lo+(j.val-lo) = j.val := by omega
    simpa only [he] using hj

theorem even_length_same_colour (P : UPath D) (colour : Fin n → Bool)
    (hcol : ∀ u v, TwoCycle D u v → colour u ≠ colour v)
    (heven : (P.vertices.length-1)%2 = 0) : colour P.first = colour P.last := by
  have hh := P.point_colour colour hcol (P.vertices.length-1) (by have h := P.length_pos; omega)
  simpa only [P.point_last,heven,if_true] using hh.symm

end ChvatalErdos.UPath

#print axioms ChvatalErdos.UPath.interval
#print axioms ChvatalErdos.UPath.even_length_same_colour
