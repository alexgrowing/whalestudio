import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def IntSeriesInv.Statement : Prop :=
  ∀ (F : PowerSeries ℤ) (r : ℝ), 0 < r → IntSeriesConv F r → coeff 0 F = 1 →
    ∃ (G : PowerSeries ℤ) (r' : ℝ), 0 < r' ∧ IntSeriesConv G r' ∧ F * G = 1

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
