import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem spinM_vacuum_lowest : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  intro n ι _ _ c hc q hq
  obtain ⟨h1, _⟩ := hc
  have two : (2 : Matrix ι ι ℂ) *ᵥ q = (2 : ℂ) • q := by
    have : (2 : Matrix ι ι ℂ) = (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
      rw [two_smul]; exact one_add_one_eq_two.symm
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
  have anti : ∀ a b d e, c a b *ᵥ (c d e *ᵥ q) =
      (if a = e ∧ b = d then (2 : ℂ) • q else 0) - c d e *ᵥ (c a b *ᵥ q) := by
    intro a b d e
    have h := congrArg (fun M => M *ᵥ q) (h1 a b d e)
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec] at h
    simp only [Matrix.mulVec_mulVec]
    rw [eq_sub_iff_add_eq, h]
    split_ifs
    · exact two
    · simp
  have sumv : ∀ (a b : Fin n), (∑ e, c a e * c e b) *ᵥ q = ∑ e, c a e *ᵥ (c e b *ᵥ q) := by
    intro a b
    simp only [Matrix.mulVec_mulVec]
    exact map_sum (Matrix.mulVec.addMonoidHomLeft q) _ _
  have hT : ∀ a e : Fin n, c a e *ᵥ (c e a *ᵥ q) =
      (if e < a then (2 : ℂ) else if e = a then 1 else 0) • q := by
    intro a e
    rcases lt_trichotomy e a with h | h | h
    · rw [if_pos h, anti a e e a, hq e a h]
      simp
    · subst h
      have h2 := anti e e e e
      simp only [and_self, if_true] at h2
      have h3 : (2 : ℂ) • (c e e *ᵥ (c e e *ᵥ q)) = (2 : ℂ) • q := by
        rw [two_smul]
        nth_rewrite 1 [h2]
        rw [two_smul]
        abel
      have h4 := smul_right_injective (ι → ℂ) (two_ne_zero : (2 : ℂ) ≠ 0) h3
      simpa using h4
    · rw [if_neg (not_lt.mpr h.le), if_neg h.ne', hq a e h]
      simp
  have hs : ∀ a : Fin n, ∑ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
      2 * ((a : ℕ) : ℂ) + 1 := by
    intro a
    have h0 : ∀ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
        (if e < a then 2 else 0) + (if e = a then 1 else 0) := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · simp [h, h.ne]
      · simp [h]
      · simp [not_lt.mpr h.le, h.ne']
    simp only [h0]
    rw [sum_add_distrib, ← Finset.sum_filter]
    have h5 : univ.filter (fun e : Fin n => e < a) = Finset.Iio a := by ext; simp
    rw [h5]
    simp [Fin.card_Iio, mul_comm]
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · unfold spinM
    rw [if_pos rfl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sumv]
    simp only [hT]
    rw [← Finset.sum_smul, hs, smul_smul, ← sub_smul]
    congr 1
    simp only [rhoV]
    push_cast
    ring
  · unfold spinM
    rw [if_neg hab.ne', sub_zero, Matrix.smul_mulVec, sumv]
    have : ∀ e : Fin n, c b e *ᵥ (c e a *ᵥ q) = 0 := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · rw [anti b e e a, if_neg (fun hh => hab.ne' hh.1), hq e b (h.trans hab)]
        simp
      · subst h
        rw [anti b e e e, if_neg (fun hh => hab.ne' hh.1), hq e b hab]
        simp
      · rw [hq a e h]
        simp
    simp [this]

end GlobalTheory.CompanionTheory.RealCount
