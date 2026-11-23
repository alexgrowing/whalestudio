import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousEqOfSchwartzPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_eq_of_schwartz_pairing : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (P Q : K → ℂ), Continuous P → Continuous Q → (∀ Φ ∈ SBE K, ∫ z, Φ z * P z ∂μ = ∫ z, Φ z * Q z ∂μ) → P = Q := by
  first | exact @GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq | exact GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq | (intros; apply GlobalTheory.CompanionTheory.SBSep.eq_of_integral_SBE_eq <;> assumption)
