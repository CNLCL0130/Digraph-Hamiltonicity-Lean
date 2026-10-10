import ChvatalErdos.RecordSeparations
import ChvatalErdos.Budgets

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints

def WordMatches {w : Nat} (word : Fin w → Fin 3) (offset : Nat) (actions : List (Fin 3)) : Prop :=
  ∀ k (hk : k < actions.length), ∃ h : offset+k < w, word ⟨offset+k,h⟩ = actions[k]

theorem WordMatches.head {w offset : Nat} {word : Fin w → Fin 3} {c : Fin 3} {cs : List (Fin 3)}
    (h : WordMatches word offset (c :: cs)) : ∃ ho : offset < w, word ⟨offset,ho⟩ = c := by
  simpa using h 0 (by simp)

theorem WordMatches.tail {w offset : Nat} {word : Fin w → Fin 3} {c : Fin 3} {cs : List (Fin 3)}
    (h : WordMatches word offset (c :: cs)) : WordMatches word (offset+1) cs := by
  intro k hk
  obtain ⟨hidx,he⟩ := h (k+1) (by simpa using hk)
  refine ⟨by omega,?_⟩
  simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

theorem exists_word {w : Nat} (cs : List (Fin 3)) (hlen : cs.length ≤ w) :
    ∃ word : Fin w → Fin 3, WordMatches word 0 cs := by
  let word : Fin w → Fin 3 := fun k => if h : k.val < cs.length then cs[k.val] else 0
  refine ⟨word,?_⟩
  intro k hk
  refine ⟨by omega,?_⟩
  simp [word,hk]

namespace Separation
variable {n m b l : Nat} {D : Digraph (Fin n)} {Q : Fin m → UCycle D b} {hb : 4 ≤ b}
    {a : Nat} {j : Fin l} {sample : Fin m → Choice b l}

noncomputable def actionLog (S : Separation D Q hb a j sample) (N : Nat) :
    Nat → State n m → List (Fin 3)
  | 0, _ => []
  | fuel+1, s => match query D Q N s with
    | none => []
    | some i =>
      let tail := actionLog S N fuel (S.guidedAdvance s i (sample i))
      if Effective D Q hb j s i (sample i) then S.code i :: tail else tail

theorem guided_used (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (N : Nat) (s : State n m) (hs : S.Good s) (i : Fin m) (hq : query D Q N s = some i) :
    (S.guidedAdvance s i (sample i)).used = s.used +
      if Effective D Q hb j s i (sample i) then 1 else 0 := by
  by_cases heff : Effective D Q hb j s i (sample i)
  · have hroom := S.room_for_effective_action ha hα hdis s hs.1 hs.2.2.1 hs.2.2.2.2
      hs.2.1 i (query_some D Q N s i hq).2.2.1 heff
    simp [guidedAdvance,advance,heff,hroom,validate,action_used]
  · simp [guidedAdvance,advance,heff,validate]

theorem actionLog_count (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (N fuel : Nat) (s : State n m) (hs : S.Good s) :
    (QueryTree.run (query D Q N) S.guidedAdvance fuel s sample).used =
      s.used + (S.actionLog N fuel s).length := by
  induction fuel generalizing s with
  | zero => simp [QueryTree.run,actionLog]
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simp [QueryTree.run,actionLog,hq]
    | some i =>
      have hnext := S.guided_step_good ha hα hdis N s hs i hq
      have hcount := ih _ hnext
      have hused := S.guided_used ha hα hdis N s hs i hq
      by_cases heff : Effective D Q hb j s i (sample i) <;>
        simp only [QueryTree.run,actionLog,hq,heff,if_true,if_false,List.length_cons] <;>
        simp only [heff,if_true,if_false] at hused <;> omega

/-- A word matching the extracted actions replays both the states and the full
coordinate/outcome transcript of the guided run. -/
theorem replay_word (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (N fuel : Nat) (s : State n m) (hs : S.Good s) (word : Fin (2*a-1) → Fin 3)
    (hmatch : WordMatches word s.used (S.actionLog N fuel s)) :
    QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s sample =
      QueryTree.run (query D Q N) S.guidedAdvance fuel s sample ∧
    (QueryTree.ofAlgorithm (query D Q N) (advance D Q hb a j word) fuel s).transcript sample =
      (QueryTree.ofAlgorithm (query D Q N) S.guidedAdvance fuel s).transcript sample := by
  induction fuel generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simp [QueryTree.run,QueryTree.ofAlgorithm,hq,QueryTree.transcript]
    | some i =>
      have hnext := S.guided_step_good ha hα hdis N s hs i hq
      have hused := S.guided_used ha hα hdis N s hs i hq
      have heq : advance D Q hb a j word s i (sample i) = S.guidedAdvance s i (sample i) := by
        by_cases heff : Effective D Q hb j s i (sample i)
        · have hm : WordMatches word s.used
              (S.code i :: S.actionLog N fuel (S.guidedAdvance s i (sample i))) := by
            simpa only [actionLog,hq,heff,if_true] using hmatch
          obtain ⟨hroom,hhead⟩ := hm.head
          simp [advance,guidedAdvance,heff,hroom,hhead]
        · simp [advance,guidedAdvance,heff]
      have htail : WordMatches word (S.guidedAdvance s i (sample i)).used
          (S.actionLog N fuel (S.guidedAdvance s i (sample i))) := by
        by_cases heff : Effective D Q hb j s i (sample i)
        · have hm : WordMatches word s.used
              (S.code i :: S.actionLog N fuel (S.guidedAdvance s i (sample i))) := by
            simpa only [actionLog,hq,heff,if_true] using hmatch
          simpa only [hused,heff,if_true] using hm.tail
        · simpa only [actionLog,hq,heff,if_false,hused,Nat.add_zero] using hmatch
      obtain ⟨hrun,htrans⟩ := ih _ hnext htail
      simp only [QueryTree.run,QueryTree.ofAlgorithm,hq,QueryTree.transcript,heq,hrun,htrans,and_self]

/-- Every bad separation follows a fixed record without aborting. This is an
existence statement for one of the finite words, not a vertex-identity record. -/
theorem exists_compatible_record (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support) (N : Nat) :
    ∃ word : Fin (2*a-1) → Fin 3,
      (stateAfter D Q hb a N j word N sample).aborted = false ∧
      S.Compatible (stateAfter D Q hb a N j word N sample) := by
  have hgood := S.guided_run_good ha hα hdis N N (initial n m) S.initial_good
  have hbudget := S.good_action_budget ha hα _ hgood
  have hcount := S.actionLog_count ha hα hdis N N (initial n m) S.initial_good
  have hlen : (S.actionLog N N (initial n m)).length ≤ 2*a-1 := by
    rw [hcount] at hbudget
    simpa only [initial,Nat.zero_add] using hbudget
  obtain ⟨word,hmatch⟩ := exists_word _ hlen
  have hreplay := S.replay_word ha hα hdis N N (initial n m) S.initial_good word hmatch
  refine ⟨word,?_⟩
  change (QueryTree.run (query D Q N) (advance D Q hb a j word) N (initial n m) sample).aborted = false ∧
    S.Compatible (QueryTree.run (query D Q N) (advance D Q hb a j word) N (initial n m) sample)
  rw [hreplay.1]
  exact ⟨hgood.2.2.2.1,hgood.2.2.1⟩

end Separation
end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.Separation.exists_compatible_record
