import ChvatalErdos.FreshLaplace
import ChvatalErdos.DeferredDecisions

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos
open FiniteProbability
variable {I A : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] [Nonempty A]

theorem freeze_mem_cylinder (seen : Finset I) (fixed x : I → A) :
    freeze seen fixed x ∈ cylinder seen fixed := by
  apply (mem_cylinder _ _ _).2
  intro i hi
  simp [freeze,hi]

theorem freeze_of_mem_cylinder (seen : Finset I) (fixed x : I → A)
    (hx : x ∈ cylinder seen fixed) : freeze seen fixed x = x := by
  funext i
  by_cases hi : i ∈ seen
  · simp [freeze,hi,(mem_cylinder _ _ _).1 hx i hi]
  · simp [freeze,hi]

/-- The part of a sample outside a fixed cylinder is independent of the
coordinates defining that cylinder. This applies to arbitrary events. -/
theorem cylinder_expectation_factor (seen : Finset I) (fixed : I → A) (f : (I → A) → ℝ) :
    expectation (fun x => if x ∈ cylinder seen fixed then f x else 0) =
      prob (cylinder seen fixed) * expectation (fun x => f (freeze seen fixed x)) := by
  let swap : ((I → A) × (I → A)) → ((I → A) × (I → A)) := fun p =>
    (freeze seen p.2 p.1,freeze seen p.1 p.2)
  have hinv : Function.Involutive swap := by
    intro p
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ seen <;> simp [swap,freeze,hi]
  let e : ((I → A) × (I → A)) ≃ ((I → A) × (I → A)) := ⟨swap,swap,hinv,hinv⟩
  have hswapmem : ∀ x y : I → A, freeze seen y x ∈ cylinder seen fixed ↔ y ∈ cylinder seen fixed := by
    intro x y
    simp only [mem_cylinder]
    constructor <;> intro h i hi
    · simpa [freeze,hi] using h i hi
    · simpa [freeze,hi] using h i hi
  have hfreeze : ∀ x y : I → A, freeze seen fixed (freeze seen y x) = freeze seen fixed x := by
    intro x y
    funext i
    by_cases hi : i ∈ seen <;> simp [freeze,hi]
  have h := expectation_equiv e (fun p : (I → A) × (I → A) =>
    (if p.1 ∈ cylinder seen fixed then (1 : ℝ) else 0) * f (freeze seen fixed p.1))
  rw [expectation_prod,expectation_prod] at h
  have hleft : expectation (fun x : I → A => expectation (fun y : I → A =>
      (if (e (x,y)).1 ∈ cylinder seen fixed then (1 : ℝ) else 0) * f (freeze seen fixed (e (x,y)).1))) =
      prob (cylinder seen fixed) * expectation (fun x => f (freeze seen fixed x)) := by
    change expectation (fun x : I → A => expectation (fun y : I → A =>
      (if freeze seen y x ∈ cylinder seen fixed then (1 : ℝ) else 0) * f (freeze seen fixed (freeze seen y x)))) = _
    simp_rw [hswapmem,hfreeze,expectation_mul_const,indicator_expectation]
    exact expectation_const_mul _ _
  rw [hleft] at h
  change prob (cylinder seen fixed) * expectation (fun x => f (freeze seen fixed x)) =
    expectation (fun x : I → A => expectation (fun _ : I → A =>
      (if x ∈ cylinder seen fixed then (1 : ℝ) else 0) * f (freeze seen fixed x))) at h
  simp only [expectation_const] at h
  rw [h]
  apply congrArg expectation
  funext x
  by_cases hx : x ∈ cylinder seen fixed
  · simp [hx,freeze_of_mem_cylinder seen fixed x hx]
  · simp [hx]

theorem conditional_freeze (seen : Finset I) (fixed : I → A) (E : Finset (I → A)) :
    prob (E ∩ cylinder seen fixed) / prob (cylinder seen fixed) =
      prob (Finset.univ.filter (fun x => freeze seen fixed x ∈ E)) := by
  have h := cylinder_expectation_factor seen fixed (fun x => if x ∈ E then (1 : ℝ) else 0)
  have hleft : expectation (fun x => if x ∈ cylinder seen fixed then (if x ∈ E then (1 : ℝ) else 0) else 0) =
      prob (E ∩ cylinder seen fixed) := by
    rw [← indicator_expectation]
    congr 1
    funext x
    by_cases hx : x ∈ E <;> by_cases hh : x ∈ cylinder seen fixed <;> simp [hx,hh]
  have hright : expectation (fun x => if freeze seen fixed x ∈ E then (1 : ℝ) else 0) =
      prob (Finset.univ.filter (fun x => freeze seen fixed x ∈ E)) := by
    rw [← indicator_expectation]
    simp
  rw [hleft,hright] at h
  have hpos := (prob_pos_iff _).2 (cylinder_nonempty seen fixed)
  exact (div_eq_iff hpos.ne').2 (by rw [h]; ring)

theorem stopped_conditional_freeze (T : QueryTree I A) (fixed : I → A) (E : Finset (I → A)) :
    prob (E ∩ historyEvent T fixed) / prob (historyEvent T fixed) =
      prob (Finset.univ.filter (fun x => freeze (T.exposed fixed) fixed x ∈ E)) := by
  rw [historyEvent_eq_cylinder]
  exact conditional_freeze _ _ _

end ChvatalErdos

#print axioms ChvatalErdos.stopped_conditional_freeze
