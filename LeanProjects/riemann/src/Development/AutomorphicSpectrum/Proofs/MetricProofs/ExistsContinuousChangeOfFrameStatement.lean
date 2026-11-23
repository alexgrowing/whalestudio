import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrame
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_change_of_frame : ∀ (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ) (T₀ : Matrix (Fin m) (Fin m) ℂ), (∀ i, ContinuousAt (fun z => M z i) 0) → (∀ i, ContinuousAt (fun z => f z i) 0) → LinearIndependent ℂ (M 0) → (∀ i, f 0 i = ∑ j, T₀ j i • M 0 j) → (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) → ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | exact GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | (intros; apply GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous <;> assumption)
