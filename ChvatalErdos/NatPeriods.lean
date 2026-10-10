import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false

namespace ChvatalErdos
variable {A : Type} (f : Nat → A)

def NatPeriod (p : Nat) : Prop := ∀ i, f (i+p) = f i

theorem NatPeriod.zero : NatPeriod f 0 := by intro i; simp

theorem NatPeriod.add {p q : Nat} (hp : NatPeriod f p) (hq : NatPeriod f q) : NatPeriod f (p+q) := by
  intro i
  rw [← Nat.add_assoc,hq,hp]

theorem NatPeriod.mul {p : Nat} (hp : NatPeriod f p) (q : Nat) : NatPeriod f (p*q) := by
  induction q with
  | zero => simpa using NatPeriod.zero f
  | succ q ih => simpa only [Nat.mul_succ] using ih.add f hp

theorem NatPeriod.sub {p q : Nat} (hp : NatPeriod f p) (hq : NatPeriod f q) (hqp : q ≤ p) :
    NatPeriod f (p-q) := by
  intro i
  have he : i+(p-q)+q = i+p := by omega
  rw [← hq (i+(p-q)),he,hp]

theorem NatPeriod.mod {p q : Nat} (hp : NatPeriod f p) (hq : NatPeriod f q) : NatPeriod f (p%q) := by
  have hm := hp.sub f (hq.mul f (p/q)) (Nat.mul_div_le p q)
  have he : p-q*(p/q) = p%q := by have hh := Nat.mod_add_div p q; omega
  rwa [he] at hm

theorem least_period (p : Nat) (hp : 0 < p) (hfp : NatPeriod f p) :
    ∃ m, 0 < m ∧ NatPeriod f m ∧ ∀ q, NatPeriod f q → m ∣ q := by
  classical
  have hex : ∃ m : Nat, 0 < m ∧ NatPeriod f m := ⟨p,hp,hfp⟩
  obtain ⟨hm,hfm⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex,hm,hfm,?_⟩
  intro q hfq
  have hmod := hfq.mod f hfm
  have hz : q%Nat.find hex = 0 := by
    by_contra hn
    have hm' := Nat.find_min' hex ⟨Nat.pos_of_ne_zero hn,hmod⟩
    have hlt := Nat.mod_lt q hm
    omega
  exact Nat.dvd_of_mod_eq_zero hz

theorem NatPeriod.reduce {p : Nat} (hp : NatPeriod f p) (i : Nat) : f i = f (i%p) := by
  have h := hp.mul f (i/p) (i%p)
  rwa [Nat.mod_add_div] at h

theorem NatPeriod.of_dvd {p q : Nat} (hp : NatPeriod f p) (hpq : p ∣ q) : NatPeriod f q := by
  obtain ⟨s,rfl⟩ := hpq
  exact hp.mul f s

theorem NatPeriod.eq_of_modEq {m i j : Nat} (hm : NatPeriod f m) (hij : Nat.ModEq m i j) :
    f i = f j := by rw [hm.reduce f i,hm.reduce f j]; exact congrArg f hij

theorem least_short_period (b L : Nat) (hb : 0 < b) (hL : 0 < L) (hLb : L < b)
    (hfb : NatPeriod f b) (hfL : NatPeriod f L) (hne : ∃ i j, f i ≠ f j) :
    ∃ m, 2 ≤ m ∧ 2*m ≤ b ∧ NatPeriod f m ∧ m ∣ b ∧ m ∣ L ∧
      ∀ q, NatPeriod f q ↔ m ∣ q := by
  obtain ⟨m,hm,hfm,hmin⟩ := least_period f b hb hfb
  have hmb := hmin b hfb
  have hmL := hmin L hfL
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m = 1 := by omega
    obtain ⟨i,j,hij⟩ := hne
    have hi := hfm.reduce f i
    have hj := hfm.reduce f j
    simp only [hm1,Nat.mod_one] at hi hj
    exact hij (hi.trans hj.symm)
  have hml : m ≤ L := Nat.le_of_dvd hL hmL
  obtain ⟨q,hbq⟩ := hmb
  have hq : 2 ≤ q := by
    by_contra h
    have hqcase : q = 0 ∨ q = 1 := by omega
    rcases hqcase with rfl | rfl <;> simp_all
    omega
  refine ⟨m,hm2,?_,hfm,⟨q,hbq⟩,hmL,fun q => ⟨hmin q,hfm.of_dvd f⟩⟩
  rw [hbq]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left m hq

theorem period_two_alternates (f : Nat → Bool) (hf : NatPeriod f 2)
    (hne : ∃ i j, f i ≠ f j) : ∀ i, f i ≠ f (i+1) := by
  have h01 : f 0 ≠ f 1 := by
    intro he
    have hconst : ∀ i, f i = f 0 := by
      intro i
      rw [hf.reduce f i]
      have hcases : i%2 = 0 ∨ i%2 = 1 := by omega
      rcases hcases with h | h <;> simp [h,he]
    obtain ⟨i,j,hij⟩ := hne
    exact hij ((hconst i).trans (hconst j).symm)
  intro i
  rw [hf.reduce f i,hf.reduce f (i+1)]
  by_cases hi : i%2 = 0
  · have hn : (i+1)%2 = 1 := by omega
    simpa only [hi,hn] using h01
  · have hi' : i%2 = 1 := by omega
    have hn : (i+1)%2 = 0 := by omega
    simpa only [hi',hn] using h01.symm

end ChvatalErdos

#print axioms ChvatalErdos.least_period
