import ChvatalErdos.RecordInvariants
import ChvatalErdos.FreshLaplace

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints FiniteProbability
variable {n m b l w : Nat}

theorem run_of_aborted (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (fuel : Nat) (s : State n m)
    (x : Fin m → Choice b l) (hs : s.aborted = true) :
    QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x = s := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [QueryTree.run,query,hs]

theorem nonabort_of_run (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (fuel : Nat) (s : State n m)
    (x : Fin m → Choice b l)
    (hs : (QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x).aborted = false) :
    s.aborted = false := by
  cases hh : s.aborted with
  | false => rfl
  | true => rw [run_of_aborted D Q hb a N j word fuel s x hh,hh] at hs; contradiction

theorem advance_used_nonabort (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a : Nat) (j : Fin l) (word : Fin w → Fin 3) (s : State n m) (i : Fin m)
    (c : Choice b l) (hn : (advance D Q hb a j word s i c).aborted = false) :
    (advance D Q hb a j word s i c).used = s.used + (if Effective D Q hb j s i c then 1 else 0) := by
  unfold advance at hn ⊢
  split
  · rename_i he
    split
    · simp only [validate,action]
      split <;> (try split) <;> rfl
    · rename_i hw
      simp [he,hw,validate] at hn
  · simp only [validate,Nat.add_zero]

noncomputable def success (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (j : Fin l) (s : State n m) (i : Fin m) (c : Choice b l) : Bool :=
  decide (Effective D Q hb j s i c)

/-- On a nonaborted branch making every requested query, the survival weight
is exactly the exponential of the number of effective actions. -/
theorem weight_of_full_run (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) (fuel : Nat) (s : State n m)
    (x : Fin m → Choice b l)
    (hn : (QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x).aborted = false)
    (hc : (QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x).seen.card = s.seen.card + fuel) :
    survivalWeight (query D Q N) (advance D Q hb a j word) (success D Q hb j) fuel s x *
        Real.exp (-Real.log 2 * (s.used : ℝ)) =
      Real.exp (-Real.log 2 * ((QueryTree.run (query D Q N) (advance D Q hb a j word) fuel s x).used : ℝ)) := by
  induction fuel generalizing s with
  | zero => simp [survivalWeight,QueryTree.run]
  | succ fuel ih =>
    cases hq : query D Q N s with
    | none => simp only [QueryTree.run,hq] at hc; omega
    | some i =>
      simp only [QueryTree.run,hq] at hn hc ⊢
      let t := advance D Q hb a j word s i (x i)
      have htn : t.aborted = false := nonabort_of_run D Q hb a N j word fuel t x hn
      have htc : (QueryTree.run (query D Q N) (advance D Q hb a j word) fuel t x).seen.card = t.seen.card + fuel := by
        change _ = (advance D Q hb a j word s i (x i)).seen.card + fuel
        rw [advance_seen,Finset.card_insert_of_notMem (query_some D Q N s i hq).2.2.1]
        dsimp only [t]
        omega
      have he := ih t hn htc
      have hu := advance_used_nonabort D Q hb a j word s i (x i) htn
      simp only [survivalWeight,hq]
      rw [← he]
      change Real.exp (-Real.log 2 * (if success D Q hb j s i (x i) then (1 : ℝ) else 0)) *
        survivalWeight (query D Q N) (advance D Q hb a j word) (success D Q hb j) fuel t x *
        Real.exp (-Real.log 2 * (s.used : ℝ)) = _
      have hexp : Real.exp (-Real.log 2 * (t.used : ℝ)) =
          Real.exp (-Real.log 2 * (if success D Q hb j s i (x i) then (1 : ℝ) else 0)) *
          Real.exp (-Real.log 2 * (s.used : ℝ)) := by
        change Real.exp (-Real.log 2 * ((advance D Q hb a j word s i (x i)).used : ℝ)) = _
        rw [hu,Nat.cast_add]
        by_cases heff : Effective D Q hb j s i (x i)
        · simp only [heff,if_pos,success,decide_true,Bool.true_eq, Nat.cast_one]
          rw [← Real.exp_add]
          congr 1
          ring
        · simp [success,heff]
      rw [hexp]
      ring

noncomputable def overflow (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (a N : Nat) (j : Fin l) (word : Fin w → Fin 3) : Finset (Fin m → Choice b l) :=
  Finset.univ.filter (fun x =>
    (stateAfter D Q hb a N j word N x).aborted = false ∧
    (stateAfter D Q hb a N j word N x).seen.card = N)

theorem overflow_tail (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (hl : 0 < l) (hthree : ¬3 ∣ b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (a N : Nat) (ha : 1 ≤ a) (hα : AlphaTwoLE D a) (j : Fin l) (word : Fin w → Fin 3)
    (hbudget : ((2*a-1 : Nat) : ℝ) ≤ (N : ℝ) / (4*b*l)) :
    prob (overflow D Q hb a N j word) ≤ Real.exp (-(N : ℝ) / (16*b*l)) := by
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero l := ⟨hl.ne'⟩
  let p : ℝ := 1 / ((2*b*l : Nat) : ℝ)
  have hbl : 1 ≤ 2*b*l := by nlinarith
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_iff₀ (by exact_mod_cast (show 0 < 2*b*l by omega))).2
    simpa using (show (1 : ℝ) ≤ ((2*b*l : Nat) : ℝ) by exact_mod_cast hbl)
  let weight := survivalWeight (query D Q N) (advance D Q hb a j word) (success D Q hb j) N (initial n m)
  have hmean : expectation weight ≤ Real.exp (-(p*N)/2) := by
    have hpow := fresh_survival_laplace (query D Q N) (advance D Q hb a j word) State.seen
      (success D Q hb j) (fun s i hi => (query_some D Q N s i hi).2.2.1)
      (advance_seen D Q hb a j word) p hp1
      (by intro s i hi; simpa [success,p] using query_effective_probability D Q hb hl hthree N j s i hi)
      N (initial n m) (fun _ => (false,(⟨0,by omega⟩,j)))
    have hpow' : expectation weight ≤ (1-p/2)^N := by
      simpa only [initial,freeze,Finset.notMem_empty,if_false] using hpow
    apply hpow'.trans
    calc
      (1-p/2)^N ≤ (Real.exp (-p/2))^N := by
        apply pow_le_pow_left₀ (by linarith)
        linarith [Real.add_one_le_exp (-p/2)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have ht := survival_weight_tail weight
    (survivalWeight_nonneg _ _ _ N (initial n m)) (p*N) (mul_nonneg hp0 (Nat.cast_nonneg _))
    hmean (overflow D Q hb a N j word) (by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have he := weight_of_full_run D Q hb a N j word N (initial n m) x hx'.1 (by simpa [initial] using hx'.2)
      have he' : weight x = Real.exp (-Real.log 2 * ((stateAfter D Q hb a N j word N x).used : ℝ)) := by
        simpa only [initial,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using he
      rw [he']
      apply Real.exp_le_exp.mpr
      have hu := nonabort_action_budget D Q hb hdis a N ha hα j word N x hx'.1
      have huR : ((stateAfter D Q hb a N j word N x).used : ℝ) ≤ ((2*a-1 : Nat) : ℝ) := by exact_mod_cast hu
      have hpN : p*N/2 = (N : ℝ)/(4*b*l) := by dsimp [p]; push_cast; ring
      rw [hpN]
      exact mul_le_mul_of_nonpos_left (huR.trans hbudget) (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]))
  convert ht using 1
  congr 1
  dsimp [p]
  push_cast
  ring

theorem overflow_selection_budget (D : Digraph (Fin n)) (Q : Fin m → UCycle D b) (hb : 4 ≤ b)
    (hl : 0 < l) (hthree : ¬3 ∣ b)
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (a : Nat) (ha : 1 ≤ a) (hα : AlphaTwoLE D a) (j : Fin l) (word : Fin w → Fin 3) :
    prob (overflow D Q hb a (4096*b*a*l^2) j word) ≤ Real.exp (-256*(a : ℝ)*l) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hbudget : ((2*a-1 : Nat) : ℝ) ≤ ((4096*b*a*l^2 : Nat) : ℝ)/(4*b*l) := by
    have hc : ((2*a-1 : Nat) : ℝ) ≤ 2*(a : ℝ) := by exact_mod_cast (Nat.sub_le (2*a) 1)
    have heq : ((4096*b*a*l^2 : Nat) : ℝ)/(4*b*l) = 1024*(a : ℝ)*l := by
      push_cast
      field_simp
      <;> ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hl1 ha0
    nlinarith
  have ht := overflow_tail D Q hb hl hthree hdis a (4096*b*a*l^2) ha hα j word hbudget
  convert ht using 1
  congr 1
  push_cast
  field_simp
  <;> ring

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.weight_of_full_run
#print axioms ChvatalErdos.Record.overflow_tail
#print axioms ChvatalErdos.Record.overflow_selection_budget
