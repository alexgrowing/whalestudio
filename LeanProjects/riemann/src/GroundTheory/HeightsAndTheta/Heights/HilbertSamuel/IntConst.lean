import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

def L2GramLattice.Statement : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module.Free ℤ E] [Module.Finite ℤ E] (X : Type) [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : E →+ (X → ℂ)),
    (∀ s, AEStronglyMeasurable (w s) μ) → (∀ s, ∃ C : ℝ, ∀ᵐ z ∂μ, ‖w s z‖ ≤ C) →
    (∀ (r : ℕ) (x : Fin r → E), LinearIndependent ℤ x → ∀ c : Fin r → ℝ,
      (∀ᵐ z ∂μ, ∑ i, (c i : ℂ) * w (x i) z = 0) → c = 0) →
    ∃ φ : E →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ E)),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w s z‖ ^ 2 ∂μ)

def L2GramLattice.intConst : ℤ →+ (Unit → ℂ) where
  toFun n := fun _ => (n : ℂ)
  map_zero' := by funext; simp
  map_add' a b := by funext; simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
