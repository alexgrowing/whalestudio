import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries

noncomputable section

def IntSeriesConv (F : PowerSeries ℤ) (r : ℝ) : Prop :=
  Summable fun n ↦ |((coeff n F : ℤ) : ℝ)| * r ^ n

def intSeriesEval (F : PowerSeries ℤ) (z : ℂ) : ℂ :=
  ∑' n, ((coeff n F : ℤ) : ℂ) * z ^ n

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
