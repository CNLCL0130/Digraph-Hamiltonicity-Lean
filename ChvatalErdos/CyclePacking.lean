import ChvatalErdos.Paths
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace ChvatalErdos

/-- A specified cycle in the graph of opposite arc pairs. -/
structure UCycle {V : Type} (D : Digraph V) (b : Nat) where
  vertex : Fin b → V
  injective : Function.Injective vertex
  edge : ∀ i, TwoCycle D (vertex i) (vertex (cyclicSucc i))

namespace UCycle
variable {V : Type} [DecidableEq V] {D : Digraph V} {b : Nat}

def support (Q : UCycle D b) : Finset V := Finset.univ.image Q.vertex

theorem mem_support (Q : UCycle D b) (v : V) : v ∈ Q.support ↔ ∃ i, Q.vertex i = v := by
  simp [support]

theorem card_support (Q : UCycle D b) : Q.support.card = b := by
  simp [support,Finset.card_image_of_injective _ Q.injective]

theorem support_nonempty (Q : UCycle D b) (hb : 0 < b) : Q.support.Nonempty := by
  rw [← Finset.card_pos,Q.card_support]
  exact hb

end UCycle

namespace CyclePacking
variable {V : Type} [Fintype V] [DecidableEq V] {D : Digraph V} {b : Nat}
noncomputable local instance : DecidableEq (UCycle D b) := Classical.typeDecidableEq _

def Valid (F : Finset (UCycle D b)) : Prop :=
  ∀ Q ∈ F, ∀ R ∈ F, Q ≠ R → Disjoint Q.support R.support

def covered (F : Finset (UCycle D b)) : Finset V := F.biUnion UCycle.support
def remainder (F : Finset (UCycle D b)) : Finset V := Finset.univ \ covered F

theorem mem_covered (F : Finset (UCycle D b)) (v : V) :
    v ∈ covered F ↔ ∃ Q ∈ F, v ∈ Q.support := by simp [covered]

theorem mem_remainder (F : Finset (UCycle D b)) (v : V) :
    v ∈ remainder F ↔ v ∉ covered F := by simp [remainder]

theorem remainder_insert (F : Finset (UCycle D b)) (Q : UCycle D b) :
    remainder (insert Q F) = remainder F \ Q.support := by
  ext v
  simp [remainder,covered,and_comm]

/-- A maximal disjoint cycle packing exists, and the remainder contains no
cycle of the prescribed length. -/
theorem maximal (D : Digraph V) (b : Nat) (hb : 0 < b) :
    ∃ F : Finset (UCycle D b), Valid F ∧
      ∀ Q : UCycle D b, ¬ Q.support ⊆ remainder F := by
  classical
  have hex : ∃ k : Nat, ∃ F : Finset (UCycle D b), Valid F ∧ (remainder F).card = k := by
    refine ⟨(remainder (∅ : Finset (UCycle D b))).card,∅,?_,rfl⟩
    simp [Valid]
  obtain ⟨F,hF,hcard⟩ := Nat.find_spec hex
  have hmin : ∀ H : Finset (UCycle D b), Valid H → (remainder F).card ≤ (remainder H).card := by
    intro H hH
    rw [hcard]
    exact Nat.find_min' hex ⟨H,hH,rfl⟩
  refine ⟨F,hF,?_⟩
  intro Q hQ
  have hdis : ∀ R ∈ F, Disjoint Q.support R.support := by
    intro R hR
    apply Finset.disjoint_left.mpr
    intro v hvQ hvR
    have hvr := (mem_remainder F v).1 (hQ hvQ)
    exact hvr ((mem_covered F v).2 ⟨R,hR,hvR⟩)
  have hnew : Valid (insert Q F) := by
    intro A hA B hB hne
    rcases Finset.mem_insert.mp hA with rfl | hAF
    · rcases Finset.mem_insert.mp hB with rfl | hBF
      · exact (hne rfl).elim
      · exact hdis B hBF
    · rcases Finset.mem_insert.mp hB with rfl | hBF
      · exact (hdis A hAF).symm
      · exact hF A hAF B hBF hne
  have hle := hmin (insert Q F) hnew
  rw [remainder_insert,Finset.card_sdiff_of_subset hQ,Q.card_support] at hle
  have hsub := Finset.card_le_card hQ
  rw [Q.card_support] at hsub
  omega

end CyclePacking
end ChvatalErdos

#print axioms ChvatalErdos.CyclePacking.maximal

