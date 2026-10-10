import ChvatalErdos.RecordInvariants

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints
variable {n m b l : Nat}

/-- A bad separation of the auxiliary paths of one colour, using cycle indices. -/
structure Separation (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (sample : Fin m → Choice b l) where
  L : Finset (Fin m)
  X : Finset (Fin m)
  R : Finset (Fin m)
  left_nonempty : L.Nonempty
  right_nonempty : R.Nonempty
  left_separator : Disjoint L X
  left_right : Disjoint L R
  separator_right : Disjoint X R
  partition : ∀ i, colour (sample i) = j ↔ i ∈ L ∨ i ∈ X ∨ i ∈ R
  small : X.card < a
  no_arc : ∀ i ∈ L, ∀ k ∈ R,
    ¬D.arc ((Q i).vertex (exit hb (sample i))) ((Q k).vertex (entrance (sample k)))

namespace Separation
variable {D : Digraph (Fin n)} {Q : Fin m → UCycle D b} {hb : 4 ≤ b}
    {a : Nat} {j : Fin l} {sample : Fin m → Choice b l}

def code (S : Separation D Q hb a j sample) (i : Fin m) : Fin 3 :=
  if i ∈ S.L then 0 else if i ∈ S.R then 1 else 2

def Compatible (S : Separation D Q hb a j sample) (s : State n m) : Prop :=
  (∀ v ∈ s.left, ∃ i ∈ s.seen, i ∈ S.L ∧ (Q i).vertex (exit hb (sample i)) = v) ∧
  (∀ v ∈ s.right, ∃ i ∈ s.seen, i ∈ S.R ∧ (Q i).vertex (entrance (sample i)) = v) ∧
  s.separator ≤ (S.X ∩ s.seen).card

theorem code_left (S : Separation D Q hb a j sample) (i : Fin m) (hi : i ∈ S.L) : S.code i = 0 := by
  simp [code,hi]

theorem code_right (S : Separation D Q hb a j sample) (i : Fin m) (hi : i ∈ S.R) : S.code i = 1 := by
  have hn : i ∉ S.L := fun h => Finset.disjoint_left.mp S.left_right h hi
  simp [code,hi,hn]

theorem code_separator (S : Separation D Q hb a j sample) (i : Fin m) (hi : i ∈ S.X) : S.code i = 2 := by
  have hnL : i ∉ S.L := fun h => Finset.disjoint_left.mp S.left_separator h hi
  have hnR : i ∉ S.R := fun h => Finset.disjoint_left.mp S.separator_right hi h
  simp [code,hnL,hnR]

theorem initial_compatible (S : Separation D Q hb a j sample) : S.Compatible (initial n m) := by
  simp [Compatible,initial]

/-- An effective left or right action belonging to a bad separation preserves
independence; the graph cut condition supplies the missing nonadjacencies. -/
theorem action_independent (S : Separation D Q hb a j sample)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hcomp : S.Compatible s)
    (hind : Independent D (fun v => v ∈ s.left ∪ s.right))
    (i : Fin m) (hfresh : i ∉ s.seen) (heff : Effective D Q hb j s i (sample i)) :
    let t := action s ((Q i).vertex (entrance (sample i))) ((Q i).vertex (exit hb (sample i))) (S.code i)
    Independent D (fun v => v ∈ t.left ∪ t.right) := by
  dsimp only
  have hcolour : colour (sample i) = j := heff.1
  have hfr := fresh_vertex D Q hdis s hs i hfresh
  rcases (S.partition i).1 hcolour with hi | hi | hi
  · rw [S.code_left i hi]
    have hav := effective_exit_avoids_union D (· ∈ s.left) (· ∈ s.right)
      ((Q i).vertex (exit hb (sample i)))
      (by
        intro v hv heq
        exact hfr (exit hb (sample i)) (heq ▸ Finset.mem_union_right s.left hv))
      (by
        intro v hv
        obtain ⟨k,_,hk,hkv⟩ := hcomp.2.1 v hv
        rw [← hkv]
        exact S.no_arc i hi k hk)
      heff.2.2
    have hn := independent_insert D (fun v => v ∈ s.left ∨ v ∈ s.right)
      ((Q i).vertex (exit hb (sample i))) (by simpa only [Finset.mem_union] using hind) hav
    simpa [action,Finset.mem_insert,Finset.mem_union,or_assoc] using hn
  · rw [S.code_separator i hi]
    simpa [action] using hind
  · rw [S.code_right i hi]
    have hav := effective_entrance_avoids_union D (· ∈ s.left) (· ∈ s.right)
      ((Q i).vertex (entrance (sample i)))
      (by
        intro v hv heq
        exact hfr (entrance (sample i)) (heq ▸ Finset.mem_union_left s.right hv))
      (by
        intro v hv
        obtain ⟨k,_,hk,hkv⟩ := hcomp.1 v hv
        rw [← hkv]
        exact S.no_arc k hk i hi)
      heff.2.1
    have hn := independent_insert D (fun v => v ∈ s.left ∨ v ∈ s.right)
      ((Q i).vertex (entrance (sample i))) (by simpa only [Finset.mem_union] using hind) hav
    simpa [action,Finset.mem_insert,Finset.mem_union,or_assoc,or_left_comm,or_comm] using hn

theorem expose_compatible (S : Separation D Q hb a j sample) (s : State n m)
    (hcomp : S.Compatible s) (i : Fin m) : S.Compatible {s with seen := insert i s.seen} := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨k,hk,hkl,hkv⟩ := hcomp.1 v hv
    exact ⟨k,Finset.mem_insert_of_mem hk,hkl,hkv⟩
  · intro v hv
    obtain ⟨k,hk,hkr,hkv⟩ := hcomp.2.1 v hv
    exact ⟨k,Finset.mem_insert_of_mem hk,hkr,hkv⟩
  · apply hcomp.2.2.trans
    apply Finset.card_le_card
    intro k hk
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hk).1,
      Finset.mem_insert_of_mem (Finset.mem_inter.mp hk).2⟩

theorem exposed_action_compatible (S : Separation D Q hb a j sample) (s : State n m)
    (hcomp : S.Compatible s) (i : Fin m) (hfresh : i ∉ s.seen)
    (hcolour : colour (sample i) = j) :
    S.Compatible (action {s with seen := insert i s.seen}
      ((Q i).vertex (entrance (sample i))) ((Q i).vertex (exit hb (sample i))) (S.code i)) := by
  let base : State n m := {s with seen := insert i s.seen}
  have hbase : S.Compatible base := S.expose_compatible s hcomp i
  rcases (S.partition i).1 hcolour with hi | hi | hi
  · rw [S.code_left i hi]
    refine ⟨?_,hbase.2.1,hbase.2.2⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨i,Finset.mem_insert_self _ _,hi,rfl⟩
    · exact hbase.1 v hv
  · rw [S.code_separator i hi]
    refine ⟨hbase.1,hbase.2.1,?_⟩
    have he : S.X ∩ insert i s.seen = insert i (S.X ∩ s.seen) := by
      ext k
      simp only [Finset.mem_inter,Finset.mem_insert]
      constructor
      · rintro ⟨hk,hki | hks⟩
        · exact Or.inl hki
        · exact Or.inr ⟨hk,hks⟩
      · rintro (rfl | ⟨hk,hks⟩)
        · exact ⟨hi,Or.inl rfl⟩
        · exact ⟨hk,Or.inr hks⟩
    have hn : i ∉ S.X ∩ s.seen := fun h => hfresh (Finset.mem_inter.mp h).2
    change s.separator+1 ≤ (S.X ∩ insert i s.seen).card
    rw [he,Finset.card_insert_of_notMem hn]
    exact Nat.add_le_add_right hcomp.2.2 1
  · rw [S.code_right i hi]
    refine ⟨hbase.1,?_,hbase.2.2⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨i,Finset.mem_insert_self _ _,hi,rfl⟩
    · exact hbase.2.1 v hv

theorem compatible_separator_bound (S : Separation D Q hb a j sample) (s : State n m)
    (hcomp : S.Compatible s) : s.separator < a :=
  lt_of_le_of_lt (hcomp.2.2.trans (Finset.card_le_card Finset.inter_subset_left)) S.small

theorem action_expose (s : State n m) (x y : Fin n) (code : Fin 3) (i : Fin m) :
    action {s with seen := insert i s.seen} x y code =
      {action s x y code with seen := insert i s.seen} := by
  unfold action
  split <;> (try split) <;> rfl

theorem action_used (s : State n m) (x y : Fin n) (code : Fin 3) :
    (action s x y code).used = s.used+1 := by
  unfold action
  split <;> (try split) <;> rfl

/-- A compatible effective action always fits in a record of length 2a-1. -/
theorem room_for_effective_action (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hcomp : S.Compatible s)
    (hind : Independent D (fun v => v ∈ s.left ∪ s.right)) (hbal : Balanced s)
    (i : Fin m) (hfresh : i ∉ s.seen) (heff : Effective D Q hb j s i (sample i)) :
    s.used < 2*a-1 := by
  let t := action s ((Q i).vertex (entrance (sample i)))
    ((Q i).vertex (exit hb (sample i))) (S.code i)
  have htind : Independent D (fun v => v ∈ t.left ∪ t.right) :=
    S.action_independent hdis s hs hcomp hind i hfresh heff
  have htc := S.exposed_action_compatible s hcomp i hfresh heff.1
  rw [action_expose] at htc
  have htsep0 := S.compatible_separator_bound _ htc
  have htsep : t.separator < a := htsep0
  have hfr := fresh_vertex D Q hdis s hs i hfresh
  have htbal : Balanced t := action_balanced s _ _ (S.code i) hbal (hfr _) (hfr _)
  have htu : t.used = s.used+1 := action_used s _ _ (S.code i)
  have hcard : (t.left ∪ t.right).card ≤ a := by
    have hh := hα (t.left ∪ t.right).toList (Finset.nodup_toList _)
      (by simpa only [Finset.mem_toList] using htind)
    simpa only [Finset.length_toList] using hh
  dsimp [Balanced] at htbal
  omega

/-- Following the side prescribed by a bad separation cannot trigger any of
the three abort rules at an effective step. -/
theorem compatible_effective_no_abort (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hcomp : S.Compatible s)
    (hind : Independent D (fun v => v ∈ s.left ∪ s.right)) (hbal : Balanced s)
    (hno : s.aborted = false) (i : Fin m) (hfresh : i ∉ s.seen)
    (heff : Effective D Q hb j s i (sample i))
    (word : Fin (2*a-1) → Fin 3)
    (hword : ∀ h : s.used < 2*a-1, word ⟨s.used,h⟩ = S.code i) :
    (advance D Q hb a j word s i (sample i)).aborted = false ∧
      S.Compatible (advance D Q hb a j word s i (sample i)) := by
  have hroom := S.room_for_effective_action ha hα hdis s hs hcomp hind hbal i hfresh heff
  have htind := S.action_independent hdis s hs hcomp hind i hfresh heff
  have htc := S.exposed_action_compatible s hcomp i hfresh heff.1
  rw [action_expose] at htc
  have htsep := S.compatible_separator_bound _ htc
  have hab : (action s ((Q i).vertex (entrance (sample i)))
      ((Q i).vertex (exit hb (sample i))) (S.code i)).aborted = false := by
    unfold action
    split <;> (try split) <;> exact hno
  simp only [advance,heff,if_pos,dif_pos hroom,hword hroom,action_expose]
  constructor
  · simp [validate,hab,Nat.not_le.mpr htsep]
    simpa only [Finset.mem_union] using htind
  · exact htc

def Good (S : Separation D Q hb a j sample) (s : State n m) : Prop :=
  Supported D Q s ∧ Balanced s ∧ S.Compatible s ∧ s.aborted = false ∧
    Independent D (fun v => v ∈ s.left ∪ s.right)

theorem initial_good (S : Separation D Q hb a j sample) : S.Good (initial n m) := by
  refine ⟨by simp [Supported,initial],by simp [Balanced,initial],S.initial_compatible,rfl,?_⟩
  intro u v hu
  simp [initial] at hu

/-- A fixed separation guides the actions; the record word will be extracted
from this run afterwards. No random coordinate is resampled. -/
noncomputable def guidedAdvance (S : Separation D Q hb a j sample)
    (s : State n m) (i : Fin m) (c : Choice b l) : State n m :=
  advance D Q hb a j (fun _ : Fin (2*a-1) => S.code i) s i c

theorem guided_step_good (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (N : Nat) (s : State n m) (hs : S.Good s) (i : Fin m) (hq : query D Q N s = some i) :
    S.Good (S.guidedAdvance s i (sample i)) := by
  have hfresh := (query_some D Q N s i hq).2.2.1
  have hfr := fresh_vertex D Q hdis s hs.1 i hfresh
  let word : Fin (2*a-1) → Fin 3 := fun _ => S.code i
  have hnext : (advance D Q hb a j word s i (sample i)).aborted = false ∧
      S.Compatible (advance D Q hb a j word s i (sample i)) := by
    by_cases heff : Effective D Q hb j s i (sample i)
    · exact S.compatible_effective_no_abort ha hα hdis s hs.1 hs.2.2.1 hs.2.2.2.2
        hs.2.1 hs.2.2.2.1 i hfresh heff word (fun _ => rfl)
    · have hsep := S.compatible_separator_bound s hs.2.2.1
      have hc := S.expose_compatible s hs.2.2.1 i
      simp only [advance,heff,if_false]
      refine ⟨?_,hc⟩
      simp [validate,hs.2.2.2.1,Nat.not_le.mpr hsep]
      simpa only [Finset.mem_union] using hs.2.2.2.2
  refine ⟨advance_supported D Q hb a j word s i (sample i) hs.1,
    advance_balanced D Q hb a j word s i (sample i) hs.2.1 (hfr _) (hfr _),
    hnext.2,hnext.1,?_⟩
  exact (advance_nonabort_valid D Q hb a j word s i (sample i) hnext.1).1

theorem guided_run_good (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (N fuel : Nat) (s : State n m) (hs : S.Good s) :
    S.Good (QueryTree.run (query D Q N) S.guidedAdvance fuel s sample) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simpa only [QueryTree.run,hq] using hs
    | some i =>
      simp only [QueryTree.run,hq]
      exact ih _ (S.guided_step_good ha hα hdis N s hs i hq)

theorem good_action_budget (S : Separation D Q hb a j sample)
    (ha : 1 ≤ a) (hα : AlphaTwoLE D a) (s : State n m) (hs : S.Good s) :
    s.used ≤ 2*a-1 := by
  have hcard : (s.left ∪ s.right).card ≤ a := by
    have hh := hα (s.left ∪ s.right).toList (Finset.nodup_toList _)
      (by simpa only [Finset.mem_toList] using hs.2.2.2.2)
    simpa only [Finset.length_toList] using hh
  have hsep := S.compatible_separator_bound s hs.2.2.1
  have hbal := hs.2.1
  unfold Balanced at hbal
  omega

theorem pure_left_forced (S : Separation D Q hb a j sample)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hcomp : S.Compatible s)
    (i : Fin m) (hfresh : i ∉ s.seen) (hpure : ∀ t, left D Q s i t)
    (hcolour : colour (sample i) = j) : i ∈ S.L ∨ i ∈ S.X := by
  rcases (S.partition i).1 hcolour with hi | hi | hi
  · exact Or.inl hi
  · exact Or.inr hi
  · have ht := hpure (entrance (sample i))
    obtain ⟨v,hv,hclose⟩ := ht.1
    have hfr := fresh_vertex D Q hdis s hs i hfresh (entrance (sample i))
    obtain ⟨k,_,hk,hkv⟩ := hcomp.1 v hv
    rcases hclose with heq | hedge
    · exact (hfr (heq ▸ Finset.mem_union_left s.right hv)).elim
    · have he := hedge.2
      rw [← hkv] at he
      exact (S.no_arc k hk i hi he).elim

theorem pure_right_forced (S : Separation D Q hb a j sample)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (s : State n m) (hs : Supported D Q s) (hcomp : S.Compatible s)
    (i : Fin m) (hfresh : i ∉ s.seen) (hpure : ∀ t, right D Q s i t)
    (hcolour : colour (sample i) = j) : i ∈ S.R ∨ i ∈ S.X := by
  rcases (S.partition i).1 hcolour with hi | hi | hi
  · have ht := hpure (exit hb (sample i))
    obtain ⟨v,hv,hclose⟩ := ht.1
    have hfr := fresh_vertex D Q hdis s hs i hfresh (exit hb (sample i))
    obtain ⟨k,_,hk,hkv⟩ := hcomp.2.1 v hv
    rcases hclose with heq | hedge
    · exact (hfr (heq ▸ Finset.mem_union_right s.left hv)).elim
    · have he := hedge.1
      rw [← hkv] at he
      exact (S.no_arc i hi k hk he).elim
  · exact Or.inr hi
  · exact Or.inl hi

end Separation
end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.Separation.action_independent
#print axioms ChvatalErdos.Record.Separation.compatible_effective_no_abort
#print axioms ChvatalErdos.Record.Separation.guided_run_good
