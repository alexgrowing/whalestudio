import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMap
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MapCompare.main | exact GlobalTheory.CompanionTheory.Ar.MapCompare.main | (intros; apply GlobalTheory.CompanionTheory.Ar.MapCompare.main <;> assumption)
