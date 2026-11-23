import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormHasSumEqOfDominantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueMaxTermUntiltFrobeniusSeriesStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem norm_sh_le_of_lam_le : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (ρ : ℝ) (x : Fl l), 2 ≤ h → 0 ≤ ρ → ρ < 1 → ‖sh x‖ < 1 → (∀ j : ℕ, j < 2 → ‖lam h j x‖ ≤ gam l h j ρ) → ‖sh x‖ ≤ ρ := by
  intro l _ h ρ x h2 hρ0 hρ1 hs1 hlam
  by_contra hlt
  push_neg at hlt
  set s := ‖sh x‖ with hs
  have hs0 : 0 < s := lt_of_le_of_lt hρ0 hlt
  have h1 : 1 ≤ h := le_trans (by norm_num) h2
  obtain ⟨j, hj, n₀, hn₀⟩ := GlobalTheory.T.exists_unique_max_term_untiltFrobeniusSeries l h s h2 hs0 hs1
  obtain ⟨hsum, -, -, -⟩ := GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j s x h1 hs1 le_rfl
  have hpw := (GlobalTheory.T.tiltFrobeniusIntegerPower_laws l).2.2.2.2.2.2
  have hterm : ∀ n : ℤ, ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖
      = ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) := by
    intro n
    rw [norm_mul, norm_zpow, hpw]
  have hnorm : ‖lam h j x‖ = ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
    rw [GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term ℂ_[l] ℤ _ _ n₀ hsum (by
      intro n hn
      rw [hterm, hterm]
      exact hn₀ n hn), hterm]
  obtain ⟨-, ⟨m, hm⟩, -, -, -, hmono⟩ := GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j s h1 hs0.le hs1
  have hgs : gam l h j s ≤ ‖lam h j x‖ := by
    rw [hm, hnorm]
    by_cases hmn : m = n₀
    · rw [hmn]
    · exact (hn₀ m hmn).le
  have hgρ : gam l h j ρ < gam l h j s := ((GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j ρ h1 hρ0 hρ1).2.2.2.2.2) s hlt hs1
  have := hlam j hj
  linarith

end GlobalTheory.PSer
