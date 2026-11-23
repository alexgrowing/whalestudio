import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FactorCommutatorEqOfNonvanishing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_exponent_commutator_eq_of_quasiPeriodic : ∀ (g : ℕ) (θ ρ : (Fin g → ℂ) → ℂ) (la mu : Fin g → ℂ) (A₁ A₂ B₁ B₂ : (Fin g → ℂ) →ₗ[ℂ] ℂ) (a₁ a₂ b₁ b₂ : ℂ), Differentiable ℂ θ → θ ≠ 0 → Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → a₁ ≠ 0 → a₂ ≠ 0 → (∀ z, θ (z + la) = a₁ * Complex.exp (A₁ z) * θ z) → (∀ z, θ (z + mu) = a₂ * Complex.exp (A₂ z) * θ z) → (∀ z, θ (z + la) * ρ (z + la) = b₁ * Complex.exp (B₁ z) * (θ z * ρ z)) → (∀ z, θ (z + mu) * ρ (z + mu) = b₂ * Complex.exp (B₂ z) * (θ z * ρ z)) → B₁ mu - A₁ mu = B₂ la - A₂ la := by
  first | exact @GlobalTheory.factor_commutator_eq_of_nonvanishing | exact GlobalTheory.factor_commutator_eq_of_nonvanishing | (intros; apply GlobalTheory.factor_commutator_eq_of_nonvanishing <;> assumption)
