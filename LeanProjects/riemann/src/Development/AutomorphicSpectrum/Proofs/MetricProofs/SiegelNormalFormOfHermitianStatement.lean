import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitian
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_normal_form_of_hermitian : ∀ {I : Type} [Fintype I] [DecidableEq I] (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H : Matrix I I ℂ), H.IsHermitian → (∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re) → (∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im) → ∃ (A : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (Z : Matrix I I ℂ), Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef ∧ ∀ z, L z = A (tz Z z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord.exists_linearEquiv_tz <;> assumption)
