import ChvatalErdos.CyclePacking

set_option autoImplicit false

namespace ChvatalErdos.UPath
variable {n : Nat} {D : Digraph (Fin n)}

def point (P : UPath D) (i : Fin P.vertices.length) : Fin n := P.vertices.get i

theorem length_pos (P : UPath D) : 0 < P.vertices.length := List.length_pos_iff.mpr P.nonempty

theorem point_first (P : UPath D) : P.point ⟨0,P.length_pos⟩ = P.first := by
  simp [point,first,List.head_eq_getElem_zero]

theorem point_mem (P : UPath D) (i : Fin P.vertices.length) : P.point i ∈ P.support :=
  (P.mem_support _).2 (List.get_mem _ _)

theorem point_injective (P : UPath D) : Function.Injective P.point :=
  List.nodup_iff_injective_get.mp P.nodup

theorem point_surjective (P : UPath D) (v : Fin n) (hv : v ∈ P.support) :
    ∃ i, P.point i = v := List.mem_iff_get.mp ((P.mem_support _).1 hv)

theorem point_step (P : UPath D) (i : Nat) (hi : i+1 < P.vertices.length) :
    TwoCycle D (P.point ⟨i,by omega⟩) (P.point ⟨i+1,hi⟩) :=
  List.isChain_iff_get.mp P.chain i hi

theorem point_colour (P : UPath D) (colour : Fin n → Bool)
    (hcol : ∀ u v, TwoCycle D u v → colour u ≠ colour v)
    (i : Nat) (hi : i < P.vertices.length) :
    colour (P.point ⟨i,hi⟩) = if i%2 = 0 then colour P.first else !colour P.first := by
  induction i with
  | zero => simp [P.point_first]
  | succ i ih =>
    have hi' : i < P.vertices.length := by omega
    have he := hcol _ _ (P.point_step i hi)
    have hflip : colour (P.point ⟨i+1,hi⟩) = !colour (P.point ⟨i,hi'⟩) := by
      cases h1 : colour (P.point ⟨i,hi'⟩) <;> cases h2 : colour (P.point ⟨i+1,hi⟩) <;> simp_all
    rw [hflip,ih hi']
    by_cases hz : i%2 = 0
    · have hn : (i+1)%2 ≠ 0 := by omega
      simp [hz,hn]
    · have hn : (i+1)%2 = 0 := by omega
      simp [hz,hn]

theorem neighbour_point_odd (P : UPath D) (colour : Fin n → Bool)
    (hcol : ∀ u v, TwoCycle D u v → colour u ≠ colour v)
    (i : Fin P.vertices.length) (hi : TwoCycle D P.first (P.point i)) : i.val%2 = 1 := by
  have hc := hcol _ _ hi
  rw [P.point_colour colour hcol i.val i.isLt] at hc
  by_cases hz : i.val%2 = 0
  · simp [hz] at hc
  · omega

def cyclePrefix (P : UPath D) (L : Nat) (hL : 3 ≤ L) (hLP : L ≤ P.vertices.length)
    (he : TwoCycle D P.first (P.point ⟨L-1,by omega⟩)) : UCycle D L where
  vertex := fun i => P.point ⟨i.val,by omega⟩
  injective := by
    intro i j hij
    exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val) (P.point_injective hij))
  edge := by
    intro i
    by_cases hi : i.val+1 < L
    · have hs : (cyclicSucc i).val = i.val+1 := Nat.mod_eq_of_lt hi
      simpa only [hs] using P.point_step i.val (by omega)
    · have hiv : i.val = L-1 := by omega
      have hs : (cyclicSucc i).val = 0 := by
        have heq : i.val+1 = L := by have h := i.isLt; omega
        change (i.val+1)%L = 0
        rw [heq,Nat.mod_self]
      simpa only [hiv,hs,P.point_first] using twoCycle_symm D he

theorem cyclePrefix_support (P : UPath D) (L : Nat) (hL : 3 ≤ L) (hLP : L ≤ P.vertices.length)
    (he : TwoCycle D P.first (P.point ⟨L-1,by omega⟩)) :
    (P.cyclePrefix L hL hLP he).support ⊆ P.support := by
  intro v hv
  obtain ⟨i,rfl⟩ := (P.cyclePrefix L hL hLP he).mem_support v |>.1 hv
  exact P.point_mem _

end ChvatalErdos.UPath

#print axioms ChvatalErdos.UPath.neighbour_point_odd
#print axioms ChvatalErdos.UPath.cyclePrefix
