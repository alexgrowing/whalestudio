import Mathlib
import Formalism.LandauZeroFreeBounds.Statement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal

open Complex DirichletCharacter

namespace GlobalTheory.LandauPageRegion

theorem inRegion_mono {c c' : ℝ} (h : c ≤ c') (q : ℕ) [NeZero q] {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) : 1 - c' / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL : 0 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
    nlinarith
  have hdiv : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right h hL
  have hs' : 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  linarith

private theorem real_zero_of_mem_zeroFreeRegion {c₁ c₂ c₃ c : ℝ} (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂) (hc₃ : c ≤ c₃)
    (hA : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), χ ≠ 1 → LFunction χ s = 0 →
      (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c₁ / Real.log (q * (|s.im| + 2)))
    (hC : ∀ (q : ℕ) [NeZero q] (s : ℂ), s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
      s.re < 1 - c₃ / Real.log (q * (|s.im| + 2)))
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) (hz : Formalism.ZeroFreeDirichlet.IsLZero χ s) :
    χ ≠ 1 ∧ χ ^ 2 = 1 ∧ s.im = 0 ∧ 1 - c₂ / Real.log (2 * q) ≤ s.re ∧
      LFunction χ (s.re : ℂ) = 0 ∧ s = (s.re : ℂ) := by
  obtain ⟨hne, hL⟩ := hz
  have h1 : χ ≠ 1 := by
    rintro rfl
    have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
    have h3 := hC q s hs1 hL
    have h4 := inRegion_mono hc₃ q hs
    linarith
  have h2 : ¬ (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) := by
    intro h
    have h3 := hA q χ s h1 hL h
    have h4 := inRegion_mono hc₁ q hs
    linarith
  push Not at h2
  obtain ⟨hsq, him⟩ := h2
  have hseq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨h1, hsq, him, ?_, ?_, hseq⟩
  · have h4 := inRegion_mono hc₂ q hs
    rw [him, abs_zero, zero_add, mul_comm] at h4
    exact h4
  · rw [← hseq]
    exact hL

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet := by
  obtain ⟨c₁, hc₁, hA⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨c₂, hc₂, hB⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨c₃, hc₃, hC⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), ?_⟩
  intro q _ χ s hs hz
  have m₁ : min c₁ (min c₂ c₃) ≤ c₁ := min_le_left _ _
  have m₂ : min c₁ (min c₂ c₃) ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have m₃ : min c₁ (min c₂ c₃) ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨h1, hsq, him, hre, hL, hseq⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs hz
  have hself := hB q χ χ s.re s.re h1 h1 hsq hsq hre hre hL hL
  refine ⟨hsq, h1, him, ?_, ?_⟩
  · rw [hseq]
    exact hself.2.2
  · intro χ' s' hs' hz'
    obtain ⟨h1', hsq', -, hre', hL', hseq'⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs' hz'
    obtain ⟨hχ, hβ, -⟩ := hB q χ' χ s'.re s.re h1' h1 hsq' hsq hre' hre hL' hL
    refine ⟨hχ, ?_⟩
    rw [hseq', hseq, hβ]

end GlobalTheory.LandauPageRegion
