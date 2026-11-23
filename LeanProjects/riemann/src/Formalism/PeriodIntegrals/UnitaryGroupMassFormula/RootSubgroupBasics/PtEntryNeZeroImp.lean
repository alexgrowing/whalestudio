import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

noncomputable section

namespace PI.AmpRootCommon

open Formalism.MainNotions.S

def pv : List (ℂ × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pv bs (i - s)

theorem ptEntry_ne_zero_imp : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → j = pv bs i
  | [], i, j, h => by simp [ptEntry] at h
  | (t, s) :: bs, i, j, h => by
    unfold ptEntry at h
    unfold pv
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1] at h
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h1.1]; omega
      · rw [if_neg h2] at h; exact absurd rfl h
    · rw [if_neg h1] at h
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3] at h
        have := ptEntry_ne_zero_imp bs (i - s) (j - s) h
        rw [if_neg (by omega)]; omega
      · rw [if_neg h3] at h; exact absurd rfl h

theorem pv_spec : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
    pv bs i < (bs.map Prod.snd).sum ∧ pv bs (pv bs i) = i ∧ ptEntry bs i (pv bs i) ≠ 0
  | [], _, i, hi => by simp at hi
  | (t, s) :: bs, hb, i, hi => by
    have ht : t ≠ 0 := (hb (t, s) (by simp)).1
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    by_cases h1 : i < s
    · have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, h1]
      have e2 : pv ((t, s) :: bs) (s - 1 - i) = i := by
        simp only [pv]; rw [if_pos (by omega)]; omega
      refine ⟨by omega, by rw [e1, e2], ?_⟩
      rw [e1]; unfold ptEntry
      rw [if_pos ⟨h1, by omega⟩, if_pos (by omega)]; exact ht
    · obtain ⟨ih1, ih2, ih3⟩ := pv_spec bs hb' (i - s) (by omega)
      have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, h1]
      have e2 : pv ((t, s) :: bs) (s + pv bs (i - s)) = i := by
        simp only [pv]; rw [if_neg (by omega), Nat.add_sub_cancel_left, ih2]; omega
      refine ⟨by omega, by rw [e1, e2], ?_⟩
      rw [e1]; unfold ptEntry
      rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]; exact ih3

theorem pv_adj : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i + 1 < (bs.map Prod.snd).sum →
    (pv bs (i + 1) + 1 = pv bs i ∧ ptEntry bs (pv bs (i + 1)) (i + 1) = ptEntry bs (pv bs i) i) ∨
      pv bs i < pv bs (i + 1)
  | [], _, i, hi => by simp at hi
  | (t, s) :: bs, hb, i, hi => by
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases h1 : i + 1 < s
    · left
      have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
      have e2 : pv ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pv, h1]
      rw [e1, e2]
      refine ⟨by omega, ?_⟩
      unfold ptEntry
      rw [if_pos ⟨by omega, h1⟩, if_pos (by omega), if_pos ⟨by omega, by omega⟩, if_pos (by omega)]
    · by_cases h2 : i + 1 = s
      · right
        have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i + 1 - s) := by simp [pv, h1]
        rw [e1, e2]; omega
      · have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, show ¬ i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i - s + 1) := by
          simp only [pv]; rw [if_neg h1, show i + 1 - s = i - s + 1 by omega]
        rw [e1, e2]
        rcases pv_adj bs hb' (i - s) (by omega) with ⟨h3, h4⟩ | h3
        · left
          refine ⟨by omega, ?_⟩
          have hA : ¬ (s + pv bs (i - s + 1) < s ∧ i + 1 < s) := by omega
          have hB : s ≤ s + pv bs (i - s + 1) ∧ s ≤ i + 1 := by omega
          have hC : ¬ (s + pv bs (i - s) < s ∧ i < s) := by omega
          have hD : s ≤ s + pv bs (i - s) ∧ s ≤ i := by omega
          unfold ptEntry
          rw [if_neg hA, if_pos hB, if_neg hC, if_pos hD, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
            show i + 1 - s = i - s + 1 by omega]
          exact h4
        · right; omega

end PI.AmpRootCommon
