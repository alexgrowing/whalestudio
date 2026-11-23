import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def DeltaIntSeries.Statement : Prop :=
  ∃ D : PowerSeries ℤ, coeff 0 D = 1 ∧ (∀ r : ℝ, 0 ≤ r → r < 1 → IntSeriesConv D r) ∧
    ∀ τ : UpperHalfPlane, ModularForm.discriminant τ =
      Function.Periodic.qParam 1 τ * intSeriesEval D (Function.Periodic.qParam 1 τ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
