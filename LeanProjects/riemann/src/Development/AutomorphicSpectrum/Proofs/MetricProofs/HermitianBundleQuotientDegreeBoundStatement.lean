import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_bundle_quotient_degree_bound : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log | exact GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log | (intros; apply GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log <;> assumption)
