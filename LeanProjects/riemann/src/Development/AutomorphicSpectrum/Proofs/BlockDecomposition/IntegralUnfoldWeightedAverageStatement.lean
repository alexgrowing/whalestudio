import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnfoldWeightedAverage
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unfold_weighted_average : ∀ {G H : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] [MeasurableSpace H] (ν : Measure H) [SFinite ν]
  (u : H → G), Measurable u → ∀ (w ρ : G → ℝ≥0∞) (F : G → ℂ), Measurable w → Measurable ρ → Measurable F →
  (∀ g, ∫⁻ h, w ((u h)⁻¹ * g) ∂ν = 1) → (∀ h g, ρ (u h * g) = ρ g) →
  (∀ q, ∫ h, F (u h * q) ∂ν = 0) → ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding | exact GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding | (intros; apply GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding <;> assumption)
