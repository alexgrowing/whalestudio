import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WeightedUniformRotatedOfExpansion
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.EndpointDifferentTypesThreshold
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckDualTThrS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DiscreteSeriesUniqueLargeGap

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.BasicNotions CompanionTheory.LimBd.Main

theorem uniqueness_global : WAt.UniqG := by
  intro k r ε lam hl h hg hh H _ _ _ σ hσ H' _ _ _ σ' hσ'
  refine ReciprocityTheory.ChartRestriction.DS.discrete_series_unique_large_gap k r ε lam hl h hg (lt_of_le_of_lt ?_ hh) H σ hσ H' σ' hσ'
  have h1 : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h2 : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (2 * r + k + 1))) h2 (Nat.cast_nonneg _)
    (by positivity)
  linarith [show ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) *
    ((2 * r + k + 1 : ℕ) : ℝ) by ring]

theorem wave_bessel_period_threshold {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct) (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3)
    (hZ : ZuckT t) (hZd : ZuckDualT t) (H : WEnd.In91) (Cb : ℝ) : WEnd.WBp Cb :=
  have hS := limSteps_of CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  have hK := CompanionTheory.D.gk.admitted.k_finite_smooth
  WEnd.wBp_of hCt ht hZ hZd hS (endDiffW_of asymptotic_different_types hS Coef.smooth_coefficient_bessel hK hZ hZd)
    (endEqW_of asymptotic_equal_types GlobalTheory.CompanionTheory.WignerShift.wigExists hS Coef.smooth_coefficient_bessel hK hZ hZd) hK H uniqueness_global Cb

theorem weighted_bound_rotated_uniform_of_cubic_threshold {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct Cgf : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hZd : ZuckDualT t) (H : WEnd.In91)
    (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  WGlue.weighted_uniform_rotated_of_expansion_alt_alt (wave_bessel_period_threshold hCt ht hZ hZd H)
    (Tied.coefCC1_of hCt ht hZ CompanionTheory.D.gk.admitted.k_finite_smooth CompanionTheory.CapEig.capelli_coefficient_continuity) hOB

open ReciprocityTheory.ChartRestriction.DS in
theorem thrS_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) : G2.thrS ε + 1 < 43 * (n : ℝ) ^ 2 := by
  have hq : S7.q0 ε ≤ n := (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have hq' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg (S7.q0 ε) : (0 : ℝ) ≤ _)]
  have h1 : (n : ℝ) * (S7.q0 ε : ℝ) ≤ n * n := mul_le_mul_of_nonneg_left hq' (by positivity)
  unfold G2.thrS
  rcases max_cases (2 * (n : ℝ)) (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) with h2 | h2 <;>
    rw [h2.1] <;> nlinarith

theorem thrS_le (n : ℕ) (ε : Fin n → Bool) (hn : 1 ≤ n) : ReciprocityTheory.ChartRestriction.DS.G2.thrS ε ≤ 43 * (n : ℝ) ^ 3 := by
  have h1 := thrS_lt ε hn
  have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast hn) (by norm_num)
  linarith

theorem uniform_bessel_rank_three_of_inputs {Cgf : ℝ} (H : WEnd.In91) (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) :
    Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  weighted_bound_rotated_uniform_of_cubic_threshold (by norm_num) thrS_le CompanionTheory.Zuck.zuckT_thrS CompanionTheory.Zuck.zuckDualT_thrS H hOB

end CompanionTheory.WaveGrid
