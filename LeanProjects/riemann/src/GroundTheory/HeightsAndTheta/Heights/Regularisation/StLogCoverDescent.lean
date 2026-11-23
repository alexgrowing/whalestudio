import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def LogCoverDescent.Statement : Prop :=
  ∀ (n a : ℕ) (h : a ≤ n) (φ : (Fin n → ℂ) → ℂ), AnalyticOnNhd ℂ φ (logCover h) →
    (∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) →
    AnalyticOnNhd ℂ (fun z => φ (logLift a z)) (puncturedChart h (ball 0 1)) ∧
      ∀ w ∈ logCover h, φ (logLift a (expCover a w)) = φ w

end

end GroundTheory.Heights₂.Heights.Regular
