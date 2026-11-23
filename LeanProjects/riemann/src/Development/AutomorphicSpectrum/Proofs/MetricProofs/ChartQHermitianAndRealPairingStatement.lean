import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartQHermitianAndRealPairing
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
theorem _root_.GlobalTheory.T.chartQ_hermitian_and_real_pairing : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → (chartQ Pr A T0 0).IsHermitian ∧ (∀ x x' : chartW bas B, (chartPer bas A T0 B x ⬝ᵥ chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x')).im = L.E x x') ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → chartQ Pr A T0 0 *ᵥ star (chartPer bas A T0 B x) = 0) ∧ ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re ∧ ((v ⬝ᵥ chartQ Pr A T0 0 *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ p = chartPer bas A T0 B x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.LimitForm.limit_form <;> assumption)
