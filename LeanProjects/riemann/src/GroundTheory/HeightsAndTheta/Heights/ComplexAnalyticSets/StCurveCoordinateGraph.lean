import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def IsCoordinateGraphNear {n : ℕ} (X : Set (Fin n → ℂ)) (x : Fin n → ℂ) : Prop :=
  x ∈ X ∧ ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧ ∃ (i : Fin n) (V : Set ℂ) (g : ℂ → Fin n → ℂ),
    IsOpen V ∧ DifferentiableOn ℂ g V ∧ (∀ t ∈ V, g t i = t) ∧ ∀ z ∈ W, z ∈ X ↔ (z i ∈ V ∧ g (z i) = z)

def CurveCoordinateGraph.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ x ∈ zeroSet I, x ∈ Metric.ball q ε → x ≠ q → IsCoordinateGraphNear (zeroSet I) x

end

end GroundTheory.Heights₂.Heights
