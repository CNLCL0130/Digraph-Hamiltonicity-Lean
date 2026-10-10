import ChvatalErdos.RootedParent
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace ChvatalErdos.RootedParent
variable {n : Nat} {D : Digraph (Fin n)} {U : Finset (Fin n)} (T : RootedParent D U)

theorem iterate_mem (v : Fin n) (hv : v ∈ U) (j : Nat) : T.parent^[j] v ∈ U := by
  induction j with
  | zero => exact hv
  | succ j ih => rw [Function.iterate_succ_apply']; exact T.parent_mem _ ih

theorem iterate_depth (v : Fin n) (hv : v ∈ U) (j : Nat) (hj : j ≤ T.depth v) :
    T.depth (T.parent^[j] v) = T.depth v-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hprev := ih (by omega)
    have hpos : 0 < T.depth (T.parent^[j] v) := by omega
    have he := T.parent_depth _ (T.iterate_mem v hv j) hpos
    rw [Function.iterate_succ_apply']
    omega

def ancestor (v : Fin n) (j : Nat) : Fin n := T.parent^[T.depth v-j] v

theorem ancestor_mem (v : Fin n) (hv : v ∈ U) (j : Nat) : T.ancestor v j ∈ U := T.iterate_mem v hv _

theorem ancestor_depth (v : Fin n) (hv : v ∈ U) (j : Nat) (hj : j ≤ T.depth v) :
    T.depth (T.ancestor v j) = j := by
  rw [ancestor,T.iterate_depth v hv _ (by omega)]
  omega

theorem ancestor_self (v : Fin n) : T.ancestor v (T.depth v) = v := by simp [ancestor]

theorem ancestor_zero (v : Fin n) (hv : v ∈ U) : T.ancestor v 0 = T.root :=
  T.zero_unique _ (T.ancestor_mem v hv _) (T.ancestor_depth v hv _ (by omega))

theorem ancestor_ancestor (v : Fin n) (hv : v ∈ U) (i j : Nat) (hij : i ≤ j) (hj : j ≤ T.depth v) :
    T.ancestor (T.ancestor v j) i = T.ancestor v i := by
  unfold ancestor
  rw [T.iterate_depth v hv _ (by omega)]
  have hd : T.depth v-(T.depth v-j) = j := by omega
  rw [hd,← Function.iterate_add_apply]
  have he : j-i+(T.depth v-j) = T.depth v-i := by omega
  rw [he]

theorem ancestor_prefix {v w : Fin n} (hv : v ∈ U) (hw : w ∈ U) (i j : Nat)
    (hij : i ≤ j) (hjv : j ≤ T.depth v) (hjw : j ≤ T.depth w)
    (he : T.ancestor v j = T.ancestor w j) : T.ancestor v i = T.ancestor w i := by
  rw [← T.ancestor_ancestor v hv i j hij hjv,← T.ancestor_ancestor w hw i j hij hjw,he]

theorem ancestor_step (v : Fin n) (hv : v ∈ U) (j : Nat) (hj : j+1 ≤ T.depth v) :
    TwoCycle D (T.ancestor v j) (T.ancestor v (j+1)) := by
  have hdepth := T.ancestor_depth v hv (j+1) hj
  have he := T.parent_edge _ (T.ancestor_mem v hv _) (by omega : 0 < T.depth (T.ancestor v (j+1)))
  have hp : T.parent (T.ancestor v (j+1)) = T.ancestor v j := by
    unfold ancestor
    rw [← Function.iterate_succ_apply' T.parent]
    have hlen : T.depth v-(j+1)+1 = T.depth v-j := by omega
    simpa only [Nat.succ_eq_add_one,hlen]
  rwa [hp] at he

def segment (v : Fin n) (hv : v ∈ U) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi ≤ T.depth v) : UPath D where
  vertices := List.ofFn (fun j : Fin (hi-lo+1) => T.ancestor v (lo+j.val))
  nonempty := by intro h; have he := congrArg List.length h; simp at he
  nodup := List.nodup_ofFn.mpr (by
    intro i j hij
    have he := congrArg T.depth hij
    rw [T.ancestor_depth v hv _ (by have h := i.isLt; omega),T.ancestor_depth v hv _ (by have h := j.isLt; omega)] at he
    apply Fin.ext
    omega)
  chain := by
    apply List.isChain_iff_getElem.mpr
    intro j hj
    have hj' : j+1 < hi-lo+1 := by simpa using hj
    simpa only [List.getElem_ofFn,Nat.add_assoc] using T.ancestor_step v hv (lo+j) (by omega)

theorem segment_first (v : Fin n) (hv : v ∈ U) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi ≤ T.depth v) :
    (T.segment v hv lo hi hle hhi).first = T.ancestor v lo := by
  simp [segment,UPath.first]

theorem segment_last (v : Fin n) (hv : v ∈ U) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi ≤ T.depth v) :
    (T.segment v hv lo hi hle hhi).last = T.ancestor v hi := by
  simp only [segment,UPath.last,List.getLast_ofFn]
  congr 1
  omega

theorem segment_length (v : Fin n) (hv : v ∈ U) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi ≤ T.depth v) :
    (T.segment v hv lo hi hle hhi).vertices.length = hi-lo+1 := by simp [segment]

theorem mem_segment (v : Fin n) (hv : v ∈ U) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi ≤ T.depth v) (z : Fin n) :
    z ∈ (T.segment v hv lo hi hle hhi).support ↔ ∃ j, lo ≤ j ∧ j ≤ hi ∧ T.ancestor v j = z := by
  rw [UPath.mem_support]
  change z ∈ List.ofFn (fun j : Fin (hi-lo+1) => T.ancestor v (lo+j.val)) ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨lo+j.val,by omega,by have h := j.isLt; omega,hj⟩
  · rintro ⟨j,hlo,hhi,hj⟩
    refine ⟨⟨j-lo,by omega⟩,?_⟩
    change T.ancestor v (lo+(j-lo)) = z
    have he : lo+(j-lo) = j := by omega
    simpa only [he] using hj

end ChvatalErdos.RootedParent

#print axioms ChvatalErdos.RootedParent.ancestor_prefix
#print axioms ChvatalErdos.RootedParent.segment
