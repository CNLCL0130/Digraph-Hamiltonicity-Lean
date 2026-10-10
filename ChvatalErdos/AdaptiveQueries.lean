import ChvatalErdos.DeferredDecisions

set_option autoImplicit false

namespace ChvatalErdos.QueryTree

theorem ofAlgorithm_fresh {I A S : Type} [DecidableEq I]
    (query : S → Option I) (advance : S → I → A → S) (seen : S → Finset I)
    (hqfresh : ∀ s i, query s = some i → i ∉ seen s)
    (hadvance : ∀ s i a, seen (advance s i a) = insert i (seen s))
    (n : Nat) (s : S) (x : I → A) :
    ((ofAlgorithm query advance n s).transcript x |>.map Prod.fst).Nodup ∧
      ∀ p ∈ (ofAlgorithm query advance n s).transcript x, p.1 ∉ seen s := by
  induction n generalizing s with
  | zero => simp [ofAlgorithm,transcript]
  | succ n ih =>
    cases hq : query s with
    | none => simp [ofAlgorithm,hq,transcript]
    | some i =>
      have hi := hqfresh s i hq
      obtain ⟨htail,havoid⟩ := ih (advance s i (x i))
      simp only [ofAlgorithm,hq,transcript,List.map_cons]
      constructor
      · apply List.nodup_cons.mpr
        refine ⟨?_,htail⟩
        intro hmem
        obtain ⟨p,hp,hpi⟩ := List.mem_map.mp hmem
        have ha := havoid p hp
        rw [hadvance,hpi] at ha
        exact ha (Finset.mem_insert_self _ _)
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hi
        · have ha := havoid p hp
          rw [hadvance] at ha
          exact fun hs => ha (Finset.mem_insert_of_mem hs)

/-- The final state of the same bounded algorithm. -/
def run {I A S : Type} (query : S → Option I) (advance : S → I → A → S) :
    Nat → S → (I → A) → S
  | 0, s, _ => s
  | n+1, s, x => match query s with
    | none => s
    | some i => run query advance n (advance s i (x i)) x

/-- A complete transcript fixes the final state, not just the queried values. -/
theorem run_reproduce {I A S : Type} (query : S → Option I) (advance : S → I → A → S)
    (n : Nat) (s : S) (x y : I → A)
    (hagree : ∀ p ∈ (ofAlgorithm query advance n s).transcript x, y p.1 = p.2) :
    run query advance n s y = run query advance n s x := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hq : query s with
    | none => simp [run,hq]
    | some i =>
      have hyi : y i = x i := hagree (i,x i) (by simp [ofAlgorithm,hq,transcript])
      simp only [run,hq,hyi]
      apply ih
      intro p hp
      exact hagree p (by simp only [ofAlgorithm,hq,transcript,List.mem_cons]; exact Or.inr hp)

theorem run_seen {I A S : Type} [DecidableEq I]
    (query : S → Option I) (advance : S → I → A → S) (seen : S → Finset I)
    (hadvance : ∀ s i a, seen (advance s i a) = insert i (seen s))
    (n : Nat) (s : S) (x : I → A) :
    seen (run query advance n s x) = seen s ∪ (ofAlgorithm query advance n s).exposed x := by
  induction n generalizing s with
  | zero => simp [run,ofAlgorithm,exposed,transcript]
  | succ n ih =>
    cases hq : query s with
    | none => simp [run,ofAlgorithm,hq,exposed,transcript]
    | some i =>
      simp only [run,ofAlgorithm,hq,ih,hadvance,exposed,transcript,List.map_cons,List.toFinset_cons]
      ext v
      simp only [Finset.mem_union,Finset.mem_insert,or_assoc,or_left_comm,or_comm]

theorem run_seen_card {I A S : Type} [DecidableEq I]
    (query : S → Option I) (advance : S → I → A → S) (seen : S → Finset I)
    (hqfresh : ∀ s i, query s = some i → i ∉ seen s)
    (hadvance : ∀ s i a, seen (advance s i a) = insert i (seen s))
    (n : Nat) (s : S) (x : I → A) :
    (seen (run query advance n s x)).card = (seen s).card +
      ((ofAlgorithm query advance n s).transcript x).length := by
  induction n generalizing s with
  | zero => simp [run,ofAlgorithm,transcript]
  | succ n ih =>
    cases hq : query s with
    | none => simp [run,ofAlgorithm,hq,transcript]
    | some i =>
      simp only [run,ofAlgorithm,hq,ih,hadvance,Finset.card_insert_of_notMem (hqfresh s i hq),
        transcript,List.length_cons]
      omega

theorem ofAlgorithm_length_le {I A S : Type}
    (query : S → Option I) (advance : S → I → A → S)
    (n : Nat) (s : S) (x : I → A) :
    ((ofAlgorithm query advance n s).transcript x).length ≤ n := by
  induction n generalizing s with
  | zero => simp [ofAlgorithm,transcript]
  | succ n ih =>
    cases hq : query s with
    | none => simp [ofAlgorithm,hq,transcript]
    | some i =>
      simpa only [ofAlgorithm,hq,transcript,List.length_cons,Nat.add_le_add_iff_right] using
        ih (advance s i (x i))

end ChvatalErdos.QueryTree

#print axioms ChvatalErdos.QueryTree.ofAlgorithm_fresh
#print axioms ChvatalErdos.QueryTree.run_reproduce
