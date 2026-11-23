import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecialization
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_extension_specialization : ∀ (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ), (∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) → ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) → ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧ (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | exact GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place | (intros; apply GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place <;> assumption)
