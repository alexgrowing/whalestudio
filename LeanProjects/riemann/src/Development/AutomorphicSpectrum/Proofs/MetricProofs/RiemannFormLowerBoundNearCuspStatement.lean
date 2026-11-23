import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormLowerBoundNearCusp
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_lower_bound_near_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → 1 ≤ m → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < ρ → 1 ≤ C * Flat.logSize a (expCover a w) * (L.riem w hw).lam1 ^ 2 ∧ (L.riem w hw).cuspW σ ≤ C * (1 + Real.log (Flat.logSize a (expCover a w))) ∧ |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w))| ≤ C * (1 + Real.log (Flat.logSize a (expCover a w))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound | exact GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound <;> assumption)
