import ChvatalErdos.Core
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace ChvatalErdos
namespace OrderedIncidence

variable {U W : Type} [LinearOrder U]

abbrev Flag (inc : U → W → Prop) := {p : U × W // inc p.1 p.2}

def Adj (inc : U → W → Prop) (e f : Flag inc) : Prop :=
  (e.val.1 < f.val.1 ∧ e.val.2 ≠ f.val.2 ∧ inc e.val.1 f.val.2) ∨
  (f.val.1 < e.val.1 ∧ f.val.2 ≠ e.val.2 ∧ inc f.val.1 e.val.2)

theorem adj_symm (inc : U → W → Prop) {e f : Flag inc} (h : Adj inc e f) :
    Adj inc f e := Or.symm h

theorem adj_irrefl (inc : U → W → Prop) (e : Flag inc) : ¬ Adj inc e e := by
  rintro (h | h) <;> exact (lt_irrefl _ h.1)

def graph (inc : U → W → Prop) : Digraph (Flag inc) :=
  ⟨Adj inc, adj_irrefl inc⟩

theorem adj_left_ne (inc : U → W → Prop) {e f : Flag inc} (h : Adj inc e f) :
    e.val.1 ≠ f.val.1 := by
  rcases h with h | h
  · exact ne_of_lt h.1
  · exact (ne_of_lt h.1).symm

theorem adj_of_lt (inc : U → W → Prop) {e f : Flag inc}
    (hef : e.val.1 < f.val.1) (h : Adj inc e f) :
    e.val.2 ≠ f.val.2 ∧ inc e.val.1 f.val.2 := by
  rcases h with h | h
  · exact h.2
  · exact False.elim (lt_asymm hef h.1)

def NoFour (inc : U → W → Prop) : Prop :=
  ∀ u v w x, u ≠ v → w ≠ x → inc u w → inc u x → inc v w → inc v x → False

theorem sorted_triangle_impossible (inc : U → W → Prop) (hn : NoFour inc)
    {e f g : Flag inc} (hef : e.val.1 < f.val.1) (hfg : f.val.1 < g.val.1)
    (aef : Adj inc e f) (afg : Adj inc f g) (aeg : Adj inc e g) : False := by
  have h₁ := adj_of_lt inc hef aef
  have h₂ := adj_of_lt inc hfg afg
  have h₃ := adj_of_lt inc (lt_trans hef hfg) aeg
  exact hn e.val.1 f.val.1 f.val.2 g.val.2 (ne_of_lt hef) h₂.1
    h₁.2 h₃.2 f.property h₂.2

theorem triangle_impossible_of_lt (inc : U → W → Prop) (hn : NoFour inc)
    {e f g : Flag inc} (hef : e.val.1 < f.val.1)
    (aef : Adj inc e f) (afg : Adj inc f g) (age : Adj inc g e) : False := by
  rcases lt_or_gt_of_ne (adj_left_ne inc afg) with hfg | hgf
  · exact sorted_triangle_impossible inc hn hef hfg aef afg (adj_symm inc age)
  · rcases lt_or_gt_of_ne (adj_left_ne inc age) with hge | heg
    · exact sorted_triangle_impossible inc hn hge hef age aef (adj_symm inc afg)
    · exact sorted_triangle_impossible inc hn heg hgf (adj_symm inc age)
        (adj_symm inc afg) aef

theorem triangle_impossible (inc : U → W → Prop) (hn : NoFour inc)
    (e f g : Flag inc) (aef : Adj inc e f) (afg : Adj inc f g)
    (age : Adj inc g e) : False := by
  rcases lt_or_gt_of_ne (adj_left_ne inc aef) with hef | hfe
  · exact triangle_impossible_of_lt inc hn hef aef afg age
  · exact triangle_impossible_of_lt inc hn hfe (adj_symm inc aef)
      (adj_symm inc age) (adj_symm inc afg)

variable [Fintype U] [Fintype W]

noncomputable instance flagFintype (inc : U → W → Prop) : Fintype (Flag inc) :=
  Fintype.ofFinite _

/-- The injection proof of the forest edge bound, without using graph forests. -/
theorem independent_card_bound (inc : U → W → Prop) (s : Finset (Flag inc))
    (hs : ∀ e ∈ s, ∀ f ∈ s, ¬ Adj inc e f) :
    s.card ≤ Fintype.card U + Fintype.card W - 1 := by
  classical
  by_cases hse : s.Nonempty
  · let active : Finset U := s.image (fun e => e.val.1)
    have ha : active.Nonempty := hse.image _
    let top := active.max' ha
    have htop : top ∈ active := Finset.max'_mem _ _
    have chosen_exists (u : U) (hu : u ∈ active) :
        ∃ e : Flag inc, e ∈ s ∧ e.val.1 = u := by
      simpa only [active, Finset.mem_image] using hu
    choose selected hselected hselected_left using chosen_exists
    let target (e : Flag inc) : U ⊕ W :=
      if h : e.val.1 ∈ active then
        if e.val.2 = (selected e.val.1 h).val.2 then Sum.inl e.val.1 else Sum.inr e.val.2
      else Sum.inr e.val.2
    have he_active (e : Flag inc) (he : e ∈ s) : e.val.1 ∈ active :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    have extra_unique {e f : Flag inc} (he : e ∈ s) (hf : f ∈ s)
        (he_extra : e.val.2 ≠ (selected e.val.1 (he_active e he)).val.2)
        (hf_extra : f.val.2 ≠ (selected f.val.1 (he_active f hf)).val.2)
        (hw : e.val.2 = f.val.2) : e.val.1 = f.val.1 := by
      by_contra hu
      rcases lt_or_gt_of_ne hu with hlt | hgt
      · have hc := hselected e.val.1 (he_active e he)
        apply hs _ hc _ hf
        apply Or.inl
        refine ⟨?_, ?_, ?_⟩
        · simpa only [hselected_left] using hlt
        · intro hh
          exact he_extra (hw.trans hh.symm)
        · simpa only [hselected_left, ← hw] using e.property
      · have hc := hselected f.val.1 (he_active f hf)
        apply hs _ hc _ he
        apply Or.inl
        refine ⟨?_, ?_, ?_⟩
        · simpa only [hselected_left] using hgt
        · intro hh
          exact hf_extra (hw.symm.trans hh.symm)
        · simpa only [hselected_left, hw] using f.property
    have hinj : Set.InjOn target (↑s : Set (Flag inc)) := by
      intro e he f hf hsame
      have hea := he_active e he
      have hfa := he_active f hf
      dsimp [target] at hsame
      rw [dif_pos hea, dif_pos hfa] at hsame
      split_ifs at hsame with heq hfq hfq
      · have hu := Sum.inl.inj hsame
        apply Subtype.ext
        apply Prod.ext hu
        exact heq.trans (by simpa only [hu] using hfq.symm)
      · have hw := Sum.inr.inj hsame
        exact Subtype.ext (Prod.ext (extra_unique he hf heq hfq hw) hw)
    have missing : Sum.inr (selected top htop).val.2 ∉ s.image target := by
      intro hmem
      obtain ⟨e, he, hh⟩ := Finset.mem_image.mp hmem
      have hea := he_active e he
      dsimp [target] at hh
      rw [dif_pos hea] at hh
      split_ifs at hh with heq
      have hw := Sum.inr.inj hh
      have hle : e.val.1 ≤ top := Finset.le_max' _ _ hea
      by_cases hu : e.val.1 = top
      · exact heq (by simpa only [hu] using hw)
      · have hlt := lt_of_le_of_ne hle hu
        have hc := hselected e.val.1 hea
        apply hs _ hc _ (hselected top htop)
        apply Or.inl
        refine ⟨?_, ?_, ?_⟩
        · simpa only [hselected_left] using hlt
        · intro hh'
          exact heq (hw.trans hh'.symm)
        · simpa only [hselected_left, ← hw] using e.property
    have hcard := Finset.card_lt_univ_of_notMem missing
    rw [Finset.card_image_of_injOn hinj, Fintype.card_sum] at hcard
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hse, Finset.card_empty]
    exact Nat.zero_le _

end OrderedIncidence
end ChvatalErdos
