import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_multiplier_integral_imaginary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ (w : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Differentiable ℂ θ → (∀ z, θ z ≠ 0) →
    (∀ l ∈ Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z) →
    ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
  first | exact @GlobalTheory.ThetaLiouville.im_form_mem_int | exact GlobalTheory.ThetaLiouville.im_form_mem_int | (intros; apply GlobalTheory.ThetaLiouville.im_form_mem_int <;> assumption)
