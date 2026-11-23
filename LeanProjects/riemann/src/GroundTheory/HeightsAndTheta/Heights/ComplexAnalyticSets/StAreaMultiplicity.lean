import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

def areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) : ℝ :=
  √(LinearMap.det (LinearMap.adjoint L ∘ₗ L))

def AreaMultiplicity.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k → finrank ℝ F = k →
    ∀ (A : Set E) (f : E → F) (f' : E → E →L[ℝ] F), MeasurableSet A →
      (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      ∫⁻ x in A, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)]) =
        ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂(μH[(k : ℝ)])

end

end GroundTheory.Heights₂.Heights
