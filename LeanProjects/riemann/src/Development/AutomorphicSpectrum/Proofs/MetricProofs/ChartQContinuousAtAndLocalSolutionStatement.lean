import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQContinuousAtAndLocalSolution
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLatticeStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartQ_continuousAt_and_local_solution : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → ContinuousAt (chartQ Pr A T0) 0 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ' → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ {u | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ chartQ Pr A T0 (expCover a w) *ᵥ star y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm.quotient_form_rep <;> assumption)
