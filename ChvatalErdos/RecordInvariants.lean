import ChvatalErdos.RecordAlgorithm

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints
variable {n m b l w : Nat}

def observed (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m) : Finset (Fin n) :=
  s.seen.biUnion (fun i => (Q i).support)

def Supported (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m) : Prop :=
  s.left ∪ s.right ⊆ observed D Q s

def Balanced (s : State n m) : Prop := s.used = (s.left ∪ s.right).card + s.separator

theorem action_union (s : State n m) (x y : Fin n) (code : Fin 3) :
    (action s x y code).left ∪ (action s x y code).right =
      if code = 0 then insert y (s.left ∪ s.right)
      else if code = 1 then insert x (s.left ∪ s.right) else s.left ∪ s.right := by
  by_cases h0 : code = 0
  · simp [action,h0]
  · by_cases h1 : code = 1 <;> simp [action,h0,h1]

theorem action_supported (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (s : State n m) (x y : Fin n) (code : Fin 3) (hs : Supported D Q s)
    (hx : x ∈ observed D Q s) (hy : y ∈ observed D Q s) :
    Supported D Q (action s x y code) := by
  have hseen : (action s x y code).seen = s.seen := by
    unfold action
    split <;> (try split) <;> rfl
  change (action s x y code).left ∪ (action s x y code).right ⊆ _
  rw [action_union]
  change (if code = 0 then insert y (s.left ∪ s.right)
    else if code = 1 then insert x (s.left ∪ s.right) else s.left ∪ s.right) ⊆
    (action s x y code).seen.biUnion (fun i => (Q i).support)
  rw [hseen]
  split
  · exact Finset.insert_subset_iff.mpr ⟨hy,hs⟩
  · split
    · exact Finset.insert_subset_iff.mpr ⟨hx,hs⟩
    · exact hs

theorem action_balanced (s : State n m) (x y : Fin n) (code : Fin 3)
    (hs : Balanced s) (hx : x ∉ s.left ∪ s.right) (hy : y ∉ s.left ∪ s.right) :
    Balanced (action s x y code) := by
  unfold Balanced at *
  rw [action_union]
  by_cases h0 : code = 0
  · simp only [action,h0,if_pos,Finset.card_insert_of_notMem hy]
    omega
  · by_cases h1 : code = 1
    · simp [action,h0,h1,Finset.card_insert_of_notMem hx]
      omega
    · simp [action,h0,h1]
      omega

theorem fresh_vertex (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hdis : ∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support)
    (s : State n m) (hs : Supported D Q s) (i : Fin m) (hi : i ∉ s.seen) (t : Fin b) :
    (Q i).vertex t ∉ s.left ∪ s.right := by
  intro hv
  obtain ⟨j,hj,hvQ⟩ := Finset.mem_biUnion.mp (hs hv)
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  exact Finset.disjoint_left.mp (hdis i j hij)
    ((Q i).mem_support _ |>.2 ⟨t,rfl⟩) hvQ

theorem advance_supported (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (word : Fin w → Fin 3) (s : State n m) (i : Fin m)
    (c : Choice b l) (hs : Supported D Q s) :
    Supported D Q (advance D Q hb a j word s i c) := by
  let base : State n m := {s with seen := insert i s.seen}
  have hsbase : Supported D Q base := by
    intro v hv
    obtain ⟨k,hk,hvQ⟩ := Finset.mem_biUnion.mp (hs hv)
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_insert_of_mem hk,hvQ⟩
  have hend : ∀ t, (Q i).vertex t ∈ observed D Q base := by
    intro t
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_insert_self _ _,(Q i).mem_support _ |>.2 ⟨t,rfl⟩⟩
  unfold advance
  split
  · split
    · exact action_supported D Q base _ _ _ hsbase (hend _) (hend _)
    · exact hsbase
  · exact hsbase

theorem advance_balanced (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (word : Fin w → Fin 3) (s : State n m) (i : Fin m)
    (c : Choice b l) (hs : Balanced s)
    (hx : (Q i).vertex (entrance c) ∉ s.left ∪ s.right)
    (hy : (Q i).vertex (exit hb c) ∉ s.left ∪ s.right) :
    Balanced (advance D Q hb a j word s i c) := by
  unfold advance
  split
  · split
    · exact action_balanced _ _ _ _ hs hx hy
    · exact hs
  · exact hs

theorem run_supported_balanced (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (hdis : ∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (fuel : Nat) (s : State n m)
    (x : Fin m → Choice b l) (hs : Supported D Q s) (hbala : Balanced s) :
    let result := QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x
    Supported D Q result ∧ Balanced result := by
  dsimp only
  induction fuel generalizing s with
  | zero => exact ⟨hs,hbala⟩
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simpa only [QueryTree.run,hq] using And.intro hs hbala
    | some i =>
      simp only [QueryTree.run,hq]
      have hfresh := fresh_vertex D Q hdis s hs i (query_some D Q N s i hq).2.2.1
      exact ih _ (advance_supported D Q hb a j word s i (x i) hs)
        (advance_balanced D Q hb a j word s i (x i) hbala (hfresh _) (hfresh _))

def NonabortValid (D : Digraph (Fin n)) (a : Nat) (s : State n m) : Prop :=
  s.aborted = false → Independent D (fun v => v ∈ s.left ∪ s.right) ∧ s.separator < a

theorem validate_nonabort_valid (D : Digraph (Fin n)) (a : Nat) (s : State n m) :
    NonabortValid D a (validate D a s) := by
  intro h
  exact validated_independent D a s h

theorem advance_nonabort_valid (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (word : Fin w → Fin 3) (s : State n m) (i : Fin m)
    (c : Choice b l) : NonabortValid D a (advance D Q hb a j word s i c) := by
  unfold advance
  exact validate_nonabort_valid D a _

theorem run_nonabort_valid (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (fuel : Nat) (s : State n m)
    (x : Fin m → Choice b l) (hs : NonabortValid D a s) :
    NonabortValid D a (QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simpa only [QueryTree.run,hq] using hs
    | some i =>
      simp only [QueryTree.run,hq]
      exact ih _ (advance_nonabort_valid D Q hb a j word s i (x i))

/-- In a nonaborted execution, the action count is bounded by the independent
set and separator budgets, with no assumption on the number of cycles. -/
theorem nonabort_action_budget (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (hdis : ∀ i j, i ≠ j → Disjoint (Q i).support (Q j).support)
    (a N : Nat) (ha : 1 ≤ a) (hα : AlphaTwoLE D a) (j : Fin l) (word : Fin w → Fin 3)
    (fuel : Nat) (x : Fin m → Choice b l)
    (hno : (stateAfter D Q hb a N j word fuel x).aborted = false) :
    (stateAfter D Q hb a N j word fuel x).used ≤ 2*a-1 := by
  let s := stateAfter D Q hb a N j word fuel x
  have hbala : Balanced s := (run_supported_balanced D Q hb hdis a N j word fuel
    (initial n m) x (by simp [Supported,initial]) (by simp [Balanced,initial])).2
  have hvalid : NonabortValid D a s := run_nonabort_valid D Q hb a N j word fuel
    (initial n m) x (by
      intro _
      refine ⟨?_,by simpa only [initial] using ha⟩
      intro u v hu
      simp [initial] at hu)
  have hvs := hvalid hno
  let I := s.left ∪ s.right
  have hcard : I.card ≤ a := by
    have hh := hα I.toList (Finset.nodup_toList _) (by simpa only [Finset.mem_toList] using hvs.1)
    simpa only [Finset.length_toList] using hh
  change s.used ≤ 2*a-1
  change s.used = I.card + s.separator at hbala
  omega

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.run_supported_balanced
#print axioms ChvatalErdos.Record.nonabort_action_budget

