import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainLineDerivativeIntegral
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_line_derivative_integral : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G),
    IsFundamentalDomain Γ D μ → ∀ (f f' : G → ℂ) (γ : ℝ → G) (b : G → ℝ), (∀ s t, γ (s + t) = γ s * γ t) →
    (∀ δ ∈ Γ, ∀ g, f (δ * g) = f g) → Continuous f → Continuous f' → IntegrableOn f D μ → IntegrableOn b D μ →
    (∀ g, HasDerivAt (fun s => f (g * γ s)) (f' g) 0) → (∀ g ∈ D, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' (g * γ t)‖ ≤ b g) →
    ∫ g in D, f' g ∂μ = 0 := by
  first | exact @GlobalTheory.setIntegral_fundamentalDomain_deriv_eq_zero | exact GlobalTheory.setIntegral_fundamentalDomain_deriv_eq_zero | (intros; apply GlobalTheory.setIntegral_fundamentalDomain_deriv_eq_zero <;> assumption)
