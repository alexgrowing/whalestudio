import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem sum_boxEnt_diag {r : ℕ} (d : Fin r → ℝ) (z a b : Fin r) (h : (a, b) ≠ (z, z)) :
    ∑ c, boxEnt d z a b c c = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg h1, if_neg h2]
  · subst hab
    have haz : a ≠ z := fun hz => h (by rw [hz])
    have : ∀ c, boxEnt d z a a c c = (if c = a then Complex.I else 0) + (if c = z then -Complex.I else 0) := by
      intro c
      simp only [boxEnt, lt_irrefl, if_false, and_self]
      by_cases h1 : c = a
      · subst h1
        simp [haz]
      · simp [h1]
    simp [this, Finset.sum_add_distrib]
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne' (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne' (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt, if_neg h1, if_neg h2]

theorem boxEnt_skew {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b a' b' : Fin r) :
    boxEnt d z a b b' a' * (d b' : ℂ) + (d a' : ℂ) * (starRingEnd ℂ) (boxEnt d z a b a' b') = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp
  · subst hab
    simp only [boxEnt, lt_irrefl, if_false]
    by_cases h1 : a' = a ∧ b' = a
    · obtain ⟨rfl, rfl⟩ := h1
      simp [mul_comm]
    · have h1' : ¬ (b' = a ∧ a' = a) := fun hc => h1 hc.symm
      simp only [if_neg h1, if_neg h1']
      by_cases h2 : a' = z ∧ b' = z
      · obtain ⟨rfl, rfl⟩ := h2
        simp [mul_comm]
      · have h2' : ¬ (b' = z ∧ a' = z) := fun hc => h2 hc.symm
        simp only [if_neg h2, if_neg h2']
        simp
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp

theorem skewCond_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  intro E _ _ _ r Ψ d z hd k τ
  by_cases hτ : τ = k.1
  · have he : ∀ a b, boxVec d z k (τ, a, b) = boxEnt (d τ) z k.2.1.1 k.2.1.2 a b := by
      intro a b
      simp only [boxVec, if_pos hτ]
      rw [hτ]
    simp only [he]
    exact ⟨sum_boxEnt_diag _ _ _ _ k.2.2, fun a b => boxEnt_skew _ (hd τ) _ _ _ _ _⟩
  · have he : ∀ a b, boxVec d z k (τ, a, b) = 0 := by
      intro a b
      simp only [boxVec, if_neg hτ]
    simp [he]

end GlobalTheory.CovTop.VolUp.FrameBox
