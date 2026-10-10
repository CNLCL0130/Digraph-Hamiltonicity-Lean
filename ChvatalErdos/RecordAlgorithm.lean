import ChvatalErdos.ComplementaryPaths
import ChvatalErdos.AdaptiveQueries

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints

structure State (n m : Nat) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  seen : Finset (Fin m)
  used : Nat
  separator : Nat
  aborted : Bool

def initial (n m : Nat) : State n m := ⟨∅,∅,∅,0,0,false⟩

variable {n m b l w : Nat}

def left (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m)
    (i : Fin m) (t : Fin b) : Prop := LeftType D (· ∈ s.left) (· ∈ s.right) ((Q i).vertex t)

def right (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m)
    (i : Fin m) (t : Fin b) : Prop := RightType D (· ∈ s.left) (· ∈ s.right) ((Q i).vertex t)

noncomputable def mixed (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (s : State n m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i ∉ s.seen ∧ (¬∀ t, left D Q s i t) ∧ (¬∀ t, right D Q s i t))

/-- Abort is tested before the cap, and the cap before normal stopping. -/
noncomputable def query (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (N : Nat)
    (s : State n m) : Option (Fin m) :=
  if s.aborted = true ∨ N ≤ s.seen.card then none
  else if h : (mixed D Q s).Nonempty then some ((mixed D Q s).min' h) else none

def Effective (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (j : Fin l) (s : State n m) (i : Fin m) (c : Choice b l) : Prop :=
  CycleEndpoints.Effective hb (left D Q s i) (right D Q s i) j c

/-- Codes 0, 1, 2 encode the paper's actions 1, 2, 3. -/
def action (s : State n m) (x y : Fin n) (code : Fin 3) : State n m :=
  if code = 0 then {s with left := insert y s.left, used := s.used+1}
  else if code = 1 then {s with right := insert x s.right, used := s.used+1}
  else {s with separator := s.separator+1, used := s.used+1}

noncomputable def validate (D : Digraph (Fin n)) (a : Nat) (s : State n m) : State n m :=
  {s with aborted := s.aborted || decide (¬Independent D (fun v => v ∈ s.left ∪ s.right) ∨ a ≤ s.separator)}

noncomputable def advance (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (word : Fin w → Fin 3) (s : State n m) (i : Fin m)
    (c : Choice b l) : State n m :=
  let base := {s with seen := insert i s.seen}
  let next := if Effective D Q hb j s i c then
      if h : s.used < w then
        action base ((Q i).vertex (entrance c)) ((Q i).vertex (exit hb c)) (word ⟨s.used,h⟩)
      else {base with aborted := true}
    else base
  validate D a next

theorem query_some (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (N : Nat)
    (s : State n m) (i : Fin m) (h : query D Q N s = some i) :
    s.aborted = false ∧ s.seen.card < N ∧ i ∉ s.seen ∧
      (¬∀ t, left D Q s i t) ∧ (¬∀ t, right D Q s i t) := by
  unfold query at h
  split at h
  · simp at h
  · rename_i hactive
    split at h
    · rename_i hmixed
      have hi : (mixed D Q s).min' hmixed = i := Option.some.inj h
      have hmem := (mixed D Q s).min'_mem hmixed
      rw [hi] at hmem
      have ht := (Finset.mem_filter.mp hmem).2
      have ha : s.aborted = false := by cases hh : s.aborted <;> simp_all
      exact ⟨ha,by omega,ht⟩
    · simp at h

theorem advance_seen (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (word : Fin w → Fin 3) (s : State n m) (i : Fin m)
    (c : Choice b l) : (advance D Q hb a j word s i c).seen = insert i s.seen := by
  unfold advance
  split
  · split
    · simp only [validate,action]
      split <;> (try split) <;> rfl
    · rfl
  · rfl

theorem validated_independent (D : Digraph (Fin n)) (a : Nat) (s : State n m)
    (h : (validate D a s).aborted = false) :
    Independent D (fun v => v ∈ s.left ∪ s.right) ∧ s.separator < a := by
  simpa [validate,Bool.or_eq_false_iff,Nat.not_le] using (show
    decide (¬Independent D (fun v => v ∈ s.left ∪ s.right) ∨ a ≤ s.separator) = false from
      (Bool.or_eq_false_iff.mp h).2)

theorem query_effective_probability (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (hthree : ¬3 ∣ b) (N : Nat) (j : Fin l)
    (s : State n m) (i : Fin m) (h : query D Q N s = some i) :
    1 / ((2*b*l : Nat) : ℝ) ≤
      FiniteProbability.prob (Finset.univ.filter (Effective D Q hb j s i)) := by
  have ht := query_some D Q N s i h
  apply effective_probability hb hl hthree _ _ _ ht.2.2.2.1 ht.2.2.2.2 j
  intro t hleft hright
  exact left_right_exclusive D (· ∈ s.left) (· ∈ s.right) ((Q i).vertex t) ⟨hleft,hright⟩

noncomputable def tree (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) : QueryTree (Fin m) (Choice b l) :=
  QueryTree.ofAlgorithm (query D Q N) (advance D Q hb a j word) N (initial n m)

theorem no_repeat_queries (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (x : Fin m → Choice b l) :
    ((tree D Q hb a N j word).transcript x |>.map Prod.fst).Nodup := by
  exact (QueryTree.ofAlgorithm_fresh (query D Q N) (advance D Q hb a j word) State.seen
    (fun s i hi => (query_some D Q N s i hi).2.2.1)
    (advance_seen D Q hb a j word) N (initial n m) x).1

noncomputable def prefixTree (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (k : Nat) : QueryTree (Fin m) (Choice b l) :=
  QueryTree.ofAlgorithm (query D Q N) (advance D Q hb a j word) k (initial n m)

noncomputable def stateAfter (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (k : Nat)
    (x : Fin m → Choice b l) : State n m :=
  QueryTree.run (query D Q N) (advance D Q hb a j word) k (initial n m) x

theorem stateAfter_seen (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (k : Nat) (x : Fin m → Choice b l) :
    (stateAfter D Q hb a N j word k x).seen = (prefixTree D Q hb a N j word k).exposed x := by
  have he := QueryTree.run_seen (query D Q N) (advance D Q hb a j word) State.seen
    (advance_seen D Q hb a j word) k (initial n m) x
  simpa only [initial,Finset.empty_union] using he

theorem history_determines_state (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (k : Nat) (x y : Fin m → Choice b l)
    (hhist : (prefixTree D Q hb a N j word k).transcript y =
      (prefixTree D Q hb a N j word k).transcript x) :
    stateAfter D Q hb a N j word k y = stateAfter D Q hb a N j word k x := by
  apply QueryTree.run_reproduce
  intro p hp
  apply QueryTree.transcript_sound (prefixTree D Q hb a N j word k) y p
  rw [hhist]
  exact hp

/-- Claim on effective outcomes conditioned only on the already exposed
history, now instantiated for the actual record algorithm. -/
theorem conditional_effective_probability (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (hthree : ¬3 ∣ b) (a N : Nat) (j : Fin l)
    (word : Fin w → Fin 3) (k : Nat) (x : Fin m → Choice b l) (i : Fin m)
    (hquery : query D Q N (stateAfter D Q hb a N j word k x) = some i) :
    let T := prefixTree D Q hb a N j word k
    let s := stateAfter D Q hb a N j word k x
    let B := Finset.univ.filter (Effective D Q hb j s i)
    1 / ((2*b*l : Nat) : ℝ) ≤
      FiniteProbability.prob (Finset.univ.filter (fun y : Fin m → Choice b l => y i ∈ B) ∩ historyEvent T x) /
        FiniteProbability.prob (historyEvent T x) := by
  dsimp only
  have hfresh := (query_some D Q N _ i hquery).2.2.1
  rw [stateAfter_seen] at hfresh
  rw [fresh_coordinate_probability _ x i hfresh]
  exact query_effective_probability D Q hb hl hthree N j _ i hquery

theorem run_stops_at_cap (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (fuel : Nat) (s : State n m)
    (x : Fin m → Choice b l) (hbudget : N ≤ s.seen.card + fuel) :
    query D Q N (QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x) = none := by
  induction fuel generalizing s with
  | zero =>
    change query D Q N s = none
    simp only [Nat.add_zero] at hbudget
    simp [query,hbudget]
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simpa [QueryTree.run,hq] using hq
    | some i =>
      simp only [QueryTree.run,hq]
      apply ih
      rw [advance_seen,Finset.card_insert_of_notMem (query_some D Q N s i hq).2.2.1]
      omega

theorem final_seen_le_cap (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (x : Fin m → Choice b l) :
    (stateAfter D Q hb a N j word N x).seen.card ≤ N := by
  have he := QueryTree.run_seen_card (query D Q N) (advance D Q hb a j word) State.seen
    (fun s i hi => (query_some D Q N s i hi).2.2.1)
    (advance_seen D Q hb a j word) N (initial n m) x
  have hlen := QueryTree.ofAlgorithm_length_le (query D Q N) (advance D Q hb a j word)
    N (initial n m) x
  have he' : (stateAfter D Q hb a N j word N x).seen.card =
      ((prefixTree D Q hb a N j word N).transcript x).length := by
    simpa only [initial,Finset.card_empty,Nat.zero_add] using he
  rw [he']
  exact hlen

/-- The bounded implementation always ends by exactly one of the paper's
tests: abort, reaching the cap, or exhausting mixed unexposed cycles. -/
theorem final_stop_cases (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (x : Fin m → Choice b l) :
    let s := stateAfter D Q hb a N j word N x
    s.aborted = true ∨
      (s.aborted = false ∧ s.seen.card = N) ∨
      (s.aborted = false ∧ s.seen.card < N ∧ mixed D Q s = ∅) := by
  dsimp only
  let s := stateAfter D Q hb a N j word N x
  have hstop : query D Q N s = none :=
    run_stops_at_cap D Q hb a N j word N (initial n m) x (by simp [initial])
  have hcap : s.seen.card ≤ N := final_seen_le_cap D Q hb a N j word x
  change s.aborted = true ∨ (s.aborted = false ∧ s.seen.card = N) ∨
    (s.aborted = false ∧ s.seen.card < N ∧ mixed D Q s = ∅)
  by_cases ha : s.aborted = true
  · exact Or.inl ha
  have ha' : s.aborted = false := by cases hh : s.aborted <;> simp_all
  by_cases hc : N ≤ s.seen.card
  · exact Or.inr (Or.inl ⟨ha',by omega⟩)
  · apply Or.inr ∘ Or.inr
    refine ⟨ha',by omega,?_⟩
    by_contra hne
    have hm : (mixed D Q s).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    simp [query,ha,hc,hm] at hstop

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.no_repeat_queries
#print axioms ChvatalErdos.Record.query_effective_probability
#print axioms ChvatalErdos.Record.history_determines_state
#print axioms ChvatalErdos.Record.conditional_effective_probability
#print axioms ChvatalErdos.Record.final_stop_cases

