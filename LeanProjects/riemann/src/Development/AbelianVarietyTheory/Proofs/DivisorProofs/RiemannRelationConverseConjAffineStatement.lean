import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relation_converse_conjAffine : ∀ {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ), M₀ᴴ = M₀ → M₀.det ≠ 0 → (Cᵀ * M₀)ᵀ = Cᵀ * M₀ → (1 - C.map star * C).det ≠ 0 → (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧ ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im := by
  first | exact @GlobalTheory.PeriodCoord.riemann_converse | exact GlobalTheory.PeriodCoord.riemann_converse | (intros; apply GlobalTheory.PeriodCoord.riemann_converse; all_goals assumption)
