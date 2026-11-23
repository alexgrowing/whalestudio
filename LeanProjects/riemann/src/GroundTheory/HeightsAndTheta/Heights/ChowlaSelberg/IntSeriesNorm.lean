import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def IntSeriesNorm.Statement : Prop :=
  ∀ (F : PowerSeries ℤ) (r : ℝ), 0 < r → IntSeriesConv F r → ∀ p : ℕ, 0 < p → ∀ j : ℕ,
    ∃ E : PowerSeries ℤ, IntSeriesConv E (r ^ p) ∧ ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ r →
      ((Multiset.range p).map fun a : ℕ ↦
          intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)).esymm j =
        intSeriesEval E (t ^ p)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
