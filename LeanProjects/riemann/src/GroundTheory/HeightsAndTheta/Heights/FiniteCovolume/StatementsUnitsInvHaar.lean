import Mathlib

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

instance secondCountableTopology_units_complex : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

instance borelSpace_units_complex : BorelSpace ℂˣ where
  measurable_eq := by
    rw [congrArg (@borel ℂˣ) Units.isOpenEmbedding_val.isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := ℂ)]
    rfl

def UnitsInvHaar.Statement (I : Type*) [Fintype I] : Prop :=
  ∀ (ρ : Measure (I → ℂˣ)) [ρ.IsHaarMeasure], ∃ c : ℝ≥0, c ≠ 0 ∧
    ∀ (k : ℕ) (g : (I → ℂˣ) → ℝ≥0∞) (g' : (I → ℂ) → ℝ≥0∞), Measurable g →
      (∀ (b : I → ℂ) (hb : ∀ i, b i ≠ 0), g' b = g fun i => (Units.mk0 (b i) (hb i))⁻¹) →
      ∫⁻ a, (∏ i, ‖(a i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g a ∂ρ =
        c * ∫⁻ b, (∏ i, ‖b i‖ₑ ^ (2 * k)) * g' b

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
