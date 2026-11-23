import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B → ContinuousOn D' B → (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) → ∀ b ∈ B, D b = D' b := by
  first | exact @GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | exact GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | (intros; apply GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq <;> assumption)
