import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul

namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc

def InWin (typ : Bool) (h η : ℕ) (u : ℤ) : Prop :=
  if typ then u ≤ (η : ℤ) else (h : ℤ) - η ≤ u

instance (typ : Bool) (h η : ℕ) : DecidablePred (InWin typ h η) := fun u => by
  unfold InWin; infer_instance

theorem count_block (w : ℤ) (t : ℕ) (a : ℤ) :
    (block w t).count a = if w ≤ a ∧ a < w + t then 1 else 0 := by
  split_ifs with ha
  · exact Multiset.count_eq_one_of_mem (Finset.Ico _ _).nodup (mem_block.2 ha)
  · exact Multiset.count_eq_zero.2 fun hm => ha (mem_block.1 hm)

def ofWindow {n r : ℕ} (t : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β) : TopData n r where
  h := h
  η := η
  ty := fun i => if typ i then LType.G else LType.Bd
  w := w
  t := t
  lows := fun i => (U i).filter (InWin (typ i) (h i) (η i))
  cloud := fun i => (U i).filter fun u => ¬ InWin (typ i) (h i) (η i) u
  two_le_h := hh
  one_le_η := hη
  one_le_letterBlockLength := ht
  card_eq := fun i => by rw [Multiset.filter_add_not, hc]
  range := fun i u hu => by
    rw [Multiset.filter_add_not, Multiset.mem_add, mem_block] at hu
    rcases hu with hu | hu
    · exact hU i u hu
    · exact ⟨(hB i u hu.1 hu.2).1, (hB i u hu.1 hu.2).2.1⟩
  lowG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨(hU i u hu.1).1, by simpa [InWin, hi'] using hu.2⟩
    · exact ⟨(hB i u hu.1 hu.2).1, by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2⟩
  cloudG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    simpa [InWin, hi'] using hu.2
  lowBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨by simpa [InWin, hi'] using hu.2, (hU i u hu.1).2⟩
    · exact ⟨by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2, (hB i u hu.1 hu.2).2.1⟩
  cloudBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    have := hu.2
    simp only [InWin, hi', Bool.false_eq_true, if_false, not_le] at this
    exact this

theorem exists_topData (l n t r : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β)
    (h1 : ∀ i, η i + 4 * GlobalTheory.PhiGam.sg l h i + 6 < l)
    (h2 : ∀ i, ∀ u ∈ U i, InWin (typ i) (h i) (η i) u → ∀ β : ℤ, w i ≤ β → β < w i + t →
      (GlobalTheory.PhiGam.sg l h i : ℤ) + 2 < |u - β|)
    (h3 : ∀ i, ∀ u ∈ U i, ¬ InWin (typ i) (h i) (η i) u → ∀ y : ℤ,
      -2 * (GlobalTheory.PhiGam.sg l h i : ℤ) - 2 ≤ y → y ≤ (η i : ℤ) + 2 * GlobalTheory.PhiGam.sg l h i + 3 →
        ¬ (if typ i then u else (h i : ℤ) - u) ≡ y [ZMOD l]) :
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) =
        ((U i).count a : ℤ) + if w i ≤ a ∧ a < w i + t then 1 else 0) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  have hUeq : ∀ i, (ofWindow t h η typ w U hh hη ht hc hU hB).U i = U i := fun i =>
    Multiset.filter_add_not _ _
  refine ⟨ofWindow t h η typ w U hh hη ht hc hU hB, rfl, fun i => ⟨rfl, hUeq i, fun a => ?_⟩,
    h1, fun i u hu β hβ => ?_, fun i u hu y hy1 hy2 => ?_⟩
  · rw [TopData.Ut, hUeq, Multiset.count_add]
    change (((U i).count a + (block (w i) t).count a : ℕ) : ℤ) = _
    rw [count_block]
    push_cast
    rfl
  · have hu' := Multiset.mem_filter.1 hu
    have hβ' := mem_block.1 hβ
    exact h2 i u hu'.1 hu'.2 β hβ'.1 hβ'.2
  · have hu' := Multiset.mem_filter.1 hu
    have := h3 i u hu'.1 hu'.2 y hy1 hy2
    have he : (ofWindow t h η typ w U hh hη ht hc hU hB).cloudRes i u =
        if typ i then u else (h i : ℤ) - u := by
      cases hi : typ i <;> simp [TopData.cloudRes, ofWindow, hi]
    rw [he]
    exact this

end GlobalTheory.TopWindow
