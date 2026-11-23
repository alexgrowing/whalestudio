import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBounds
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_minimum_and_cusp_weight_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsCMFam σ → R.HasRank σ m → 1 ≤ m → 0 < R.lam1 ∧ (∀ v : Λ, v ≠ 0 → R.lam1 ≤ Real.sqrt (R.normSq v)) ∧ (∀ I, R.IsCusp I → -Real.log (R.nz σ I) ≤ R.cuspW σ ∧ Module.finrank (𝓞 E) I ≤ m) ∧ 0 ≤ R.cuspW σ ∧ R.cuspW σ ≤ Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) + Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le | exact GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le <;> assumption)
