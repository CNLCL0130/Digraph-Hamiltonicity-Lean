import ChvatalErdos.Selection
import ChvatalErdos.GraphEmbedding

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open CycleEndpoints FiniteProbability Record
variable {n c m b l a t : Nat}

noncomputable def pathNeighbours (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (outgoing : Bool) (x : Fin m → Choice b l) (j : Fin l) (z : Fin n) : Finset (Fin m) :=
  (active x j).filter (fun w => if outgoing then D.arc z ((Q w).selectedPath hb (x w)).first
    else D.arc ((Q w).selectedPath hb (x w)).last z)

def inducedEmbedding (D : Digraph (Fin n)) (e : Fin c → Fin n) (he : Function.Injective e) :
    GraphEmbedding (inducedDigraph D e) D := ⟨e,he,fun _ _ h => h⟩

theorem core_path_count (D : Digraph (Fin n)) (e : Fin c → Fin n) (he : Function.Injective e)
    (Q : Fin m → UCycle (inducedDigraph D e) b) (hb : 4 ≤ b)
    (outgoing : Bool) (x : Fin m → Choice b l) (j : Fin l) (z : Fin n) :
    ((pathNeighbours D (fun w => (Q w).mapGraph (inducedEmbedding D e he)) hb outgoing x j z).card : ℝ) =
      successCount (fun i => directedNeighbourEvent hb outgoing
        (terminalCoordinates (inducedDigraph D e) Q (Finset.univ.filter (fun v => if outgoing then D.arc z (e v) else D.arc (e v) z)) i) j) x := by
  let E := pathNeighbours D (fun w => (Q w).mapGraph (inducedEmbedding D e he)) hb outgoing x j z
  have hmem : ∀ i, i ∈ E ↔ x i ∈ directedNeighbourEvent hb outgoing
      (terminalCoordinates (inducedDigraph D e) Q (Finset.univ.filter (fun v => if outgoing then D.arc z (e v) else D.arc (e v) z)) i) j := by
    intro i
    have hends := ((Q i).mapGraph (inducedEmbedding D e he)).selected_endpoints hb (x i)
    simp only [E,pathNeighbours,active,Finset.mem_filter,Finset.mem_univ,true_and,hends.1,hends.2]
    cases outgoing <;> simp [active,directedNeighbourEvent,neighbourEvent,exitNeighbourEvent,
      terminalCoordinates,UCycle.mapGraph,inducedEmbedding,and_comm]
  have hsum : (∑ i : Fin m, if i ∈ E then (1 : ℝ) else 0) = (E.card : ℝ) := by simp
  change (E.card : ℝ) = _
  rw [← hsum]
  simp only [successCount,hmem]

theorem core_selection_exists (D : Digraph (Fin n)) (e : Fin c → Fin n) (he : Function.Injective e)
    (Q : Fin m → UCycle (inducedDigraph D e) b)
    (hb : 4 ≤ b) (hl : 0 < l) (ha : 2 ≤ a) (hthree : ¬3 ∣ b) (hlmax : l ≤ 2*a)
    (hD : KStrong (inducedDigraph D e) (selectionBudget a b l))
    (hα : AlphaTwoLE (inducedDigraph D e) a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (T : Fin t → Fin n) (hT : t ≤ 2*a)
    (hB : ∀ (outgoing : Bool) z, selectionBudget a b l ≤
      (Finset.univ.filter (fun v => if outgoing then D.arc (T z) (e v) else D.arc (e v) (T z))).card) :
    ∃ x : Fin m → Choice b l,
      (∀ j, KStrongOn (auxiliary D (fun w => (Q w).mapGraph (inducedEmbedding D e he)) hb x) (active x j) a) ∧
      (∀ outgoing j z, a ≤ (pathNeighbours D (fun w => (Q w).mapGraph (inducedEmbedding D e he)) hb outgoing x j (e z)).card) ∧
      (∀ outgoing j z, a ≤ (pathNeighbours D (fun w => (Q w).mapGraph (inducedEmbedding D e he)) hb outgoing x j (T z)).card) := by
  let F := inducedDigraph D e
  let Q' := fun w => (Q w).mapGraph (inducedEmbedding D e he)
  obtain ⟨own,hown⟩ := cycle_owners F Q hdis hcover
  let B := fun (outgoing : Bool) z => Finset.univ.filter (fun v => if outgoing then D.arc (T z) (e v) else D.arc (e v) (T z))
  obtain ⟨x,hJ,hvertex,hterminal⟩ := selection_exists F Q hb hl ha hthree hlmax hD hα hdis hcover own B hT hB
  refine ⟨x,hJ,?_,?_⟩
  · intro outgoing j z
    have hh := hvertex outgoing j z
    rw [← actualPathNeighbours_count F Q hb hcover own hown outgoing x j z] at hh
    have hn : a ≤ (actualPathNeighbours F Q hb outgoing x j z).card := by exact_mod_cast hh
    apply hn.trans (Finset.card_le_card ?_)
    intro w hw
    have hmem := (Finset.mem_filter.mp hw).2.2
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hw).1,?_⟩
    have hends := (Q w).selected_endpoints hb (x w)
    have hends' := (Q' w).selected_endpoints hb (x w)
    change (if outgoing then D.arc (e z) ((Q' w).selectedPath hb (x w)).first else D.arc ((Q' w).selectedPath hb (x w)).last (e z))
    simp only [hends'.1,hends'.2]
    cases outgoing <;> simpa [F,inducedDigraph,Q',UCycle.mapGraph,inducedEmbedding,hends.1,hends.2] using hmem
  · intro outgoing j z
    have hh := hterminal outgoing j z
    have hc := core_path_count D e he Q hb outgoing x j (T z)
    rw [← hc] at hh
    exact_mod_cast hh

end ChvatalErdos

#print axioms ChvatalErdos.core_selection_exists
