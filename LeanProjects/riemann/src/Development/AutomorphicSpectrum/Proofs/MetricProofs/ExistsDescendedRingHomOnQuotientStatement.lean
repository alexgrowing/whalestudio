import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsDescendedRingHomOnQuotient
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_ringHom_on_quotient : ∀ (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → (∀ (a : O) z, q z = 0 → q (B a z) = 0) → ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection | exact GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection <;> assumption)
