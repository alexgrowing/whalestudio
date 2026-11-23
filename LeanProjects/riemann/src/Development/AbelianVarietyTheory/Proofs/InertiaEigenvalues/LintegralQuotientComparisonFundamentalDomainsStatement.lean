import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralQuotientComparisonFundamentalDomains
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_quotient_comparison_fundamentalDomains : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    (Γ Γ' : Subgroup H) [Countable Γ] [Countable Γ'] (D D' : Set H), IsFundamentalDomain Γ D ν →
    IsFundamentalDomain Γ' D' ν → ∀ (𝓕 𝓕' : Set G), IsFundamentalDomain (Γ.map H.subtype) 𝓕 μ →
    IsFundamentalDomain (Γ'.map H.subtype) 𝓕' μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ h : H, ∀ g, f (h * g) = f g) →
    ν D' * ∫⁻ g in 𝓕, f g ∂μ = ν D * ∫⁻ g in 𝓕', f g ∂μ := by
  first | exact @GlobalTheory.CellCompare.lintegral_comparison | exact GlobalTheory.CellCompare.lintegral_comparison | (intros; apply GlobalTheory.CellCompare.lintegral_comparison <;> assumption)
