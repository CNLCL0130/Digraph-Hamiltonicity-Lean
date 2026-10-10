import ChvatalErdos.CycleCoreHamiltonian
import ChvatalErdos.PackingCore

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open Record
variable {n b l a r : Nat}

theorem hamiltonian_from_small_remainder (D : Digraph (Fin n))
    (hb : 4 ≤ b) (ha : 2 ≤ a) (hthree : ¬3 ∣ b)
    (hlmin : Nat.clog 2 a+1 ≤ l) (hlmax : l ≤ 2*a)
    (hD : KStrong D (selectionBudget a b l+r)) (hα : AlphaTwoLE D a)
    (P : Finset (UCycle D b)) (hP : CyclePacking.Valid P)
    (hR : (CyclePacking.remainder P).card ≤ r) : Hamiltonian D := by
  obtain ⟨e,he,heR,hsurj,hc,Q,hQ,hcover⟩ := packing_core D P hP
  exact hamiltonian_with_cycle_core D hb ha hthree hlmin hlmax hD hα
    (CyclePacking.remainder P) hR e he heR hsurj hc Q hQ hcover

end ChvatalErdos

#print axioms ChvatalErdos.hamiltonian_from_small_remainder
