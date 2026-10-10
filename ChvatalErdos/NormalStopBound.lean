import ChvatalErdos.SmallSide
import ChvatalErdos.LargeSide
import ChvatalErdos.Estimates

set_option autoImplicit false
open scoped Classical

namespace ChvatalErdos.Record
open CycleEndpoints FiniteProbability
variable {n m b l a : Nat}

def selectionBudget (a b l : Nat) : Nat := 65536*b^2*a*l^2
def exposureCap (a b l : Nat) : Nat := 4096*b*a*l^2
def matchingSize (a b l : Nat) : Nat := 8192*b^2*a*l^2

theorem selectionBudget_real (a b l : Nat) : (selectionBudget a b l : ℝ) = selectionK a b l := by
  simp [selectionBudget,selectionK]

noncomputable def normalError (a b l : Nat) : ℝ :=
  2*selectionK a b l * Real.exp (-selectionK a b l/(16*b*l)) +
    Real.exp (-selectionK a b l/(64*b^2*l^2))

theorem normalError_nonneg (a b l : Nat) : 0 ≤ normalError a b l := by
  dsimp [normalError,selectionK]
  positivity

theorem normal_stopping_bound (D : Digraph (Fin n)) (Q : Fin m → UCycle D b)
    (hb : 4 ≤ b) (hl : 0 < l) (j : Fin l) (hD : KStrong D (selectionBudget a b l))
    (hdis : ∀ i k, i ≠ k → Disjoint (Q i).support (Q k).support)
    (hcover : ∀ z, ∃ i t, (Q i).vertex t = z)
    (s : State n m) (hs : Supported D Q s) (hn : mixed D Q s = ∅)
    (hcap : s.seen.card ≤ exposureCap a b l)
    (T : QueryTree (Fin m) (Choice b l)) (fixed : Fin m → Choice b l)
    (hseen : s.seen = T.exposed fixed) :
    prob (compatibleEvent D Q hb a j s ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤
      normalError a b l := by
  let M := 4096*b^2*a*l^2
  have hKM : selectionBudget a b l = 16*M := by dsimp [selectionBudget,M]; ring
  have hqM : matchingSize a b l = 2*M := by dsimp [matchingSize,M]; ring
  have hW : (observed D Q s).card ≤ M := by
    change (verticesOf D Q s.seen).card ≤ M
    rw [verticesOf_card D Q hdis]
    apply (Nat.mul_le_mul_right b hcap).trans_eq
    dsimp [exposureCap,M]
    ring
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hneighbourbudget : (a : ℝ) ≤ (selectionBudget a b l : ℝ)/(4*b*l) := by
    rw [selectionBudget_real]
    have he : selectionK a b l/(4*b*l) = 16384*(b : ℝ)*a*l := by
      dsimp [selectionK]; field_simp; ring
    rw [he]
    have hbl : (1 : ℝ) ≤ (b : ℝ)*l := by exact_mod_cast (show 1 ≤ b*l by nlinarith)
    have hm := mul_le_mul_of_nonneg_right hbl haR
    nlinarith
  have hsmall : ∀ outgoing : Bool,
      (verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card < matchingSize a b l →
      prob (compatibleEvent D Q hb a j s ∩ historyEvent T fixed) / prob (historyEvent T fixed) ≤ normalError a b l := by
    intro outgoing hside
    have hC := Finset.card_union_le (observed D Q s)
      (verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s))
    have hCnat : 2*(observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card ≤ selectionBudget a b l := by
      rw [hqM] at hside
      rw [hKM]
      omega
    have hCR : ((observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card : ℝ) ≤
        (selectionBudget a b l : ℝ)/2 := by
      have hh : 2*((observed D Q s ∪ verticesOf D Q (if outgoing then pureLeft D Q s else pureRight D Q s)).card : ℝ) ≤
          (selectionBudget a b l : ℝ) := by exact_mod_cast hCnat
      linarith
    have ht := stopped_small_side_tail D Q hb hl j hD hdis hcover s hs hn outgoing T fixed hseen hneighbourbudget hCR
    rw [selectionBudget_real] at ht
    apply ht.trans
    dsimp [normalError]
    have hpos : 0 ≤ selectionK a b l * Real.exp (-selectionK a b l/(16*b*l)) := by dsimp [selectionK]; positivity
    have hexp := (Real.exp_pos (-selectionK a b l/(64*b^2*l^2))).le
    nlinarith
  by_cases hL : (verticesOf D Q (pureLeft D Q s)).card < matchingSize a b l
  · exact hsmall true hL
  by_cases hR : (verticesOf D Q (pureRight D Q s)).card < matchingSize a b l
  · exact hsmall false hR
  have hmatchbudget : (a : ℝ) ≤ (matchingSize a b l : ℝ)/(2*b^2*l^2) := by
    have he : (matchingSize a b l : ℝ)/(2*b^2*l^2) = 4096*(a : ℝ) := by
      dsimp [matchingSize]; push_cast; field_simp; ring
    rw [he]
    linarith
  have ht := stopped_large_side_tail D Q hb hl j hD hdis hcover s hs hn
    (q := matchingSize a b l) (by rw [hqM,hKM]; omega) (by omega) (by omega) T fixed hseen hmatchbudget
  have he : -(matchingSize a b l : ℝ)/(8*b^2*l^2) = -selectionK a b l/(64*b^2*l^2) := by
    dsimp [matchingSize,selectionK]; push_cast; ring
  rw [he] at ht
  apply ht.trans
  dsimp [normalError,selectionK]
  exact le_add_of_nonneg_left (by positivity)

end ChvatalErdos.Record

#print axioms ChvatalErdos.Record.normal_stopping_bound
