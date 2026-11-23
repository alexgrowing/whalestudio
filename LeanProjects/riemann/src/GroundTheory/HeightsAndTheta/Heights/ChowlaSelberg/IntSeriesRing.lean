import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

def IntSeriesRing.Statement : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    (∃ S : Subring (PowerSeries ℤ), ∀ F, F ∈ S ↔ IntSeriesConv F r) ∧
    (∀ F G, IntSeriesConv F r → IntSeriesConv G r → ∀ z : ℂ, ‖z‖ ≤ r →
      intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z) ∧
    (∀ F, IntSeriesConv F r → ∀ z : ℂ, ‖z‖ ≤ r →
      HasSum (fun n ↦ ((coeff n F : ℤ) : ℂ) * z ^ n) (intSeriesEval F z)) ∧
    (∀ F (r' : ℝ), IntSeriesConv F r → 0 ≤ r' → r' ≤ r → IntSeriesConv F r') ∧
    (∀ (p : ℕ) (hp : p ≠ 0) F, IntSeriesConv F (r ^ p) →
      IntSeriesConv (expand p hp F) r ∧
        ∀ z : ℂ, ‖z‖ ≤ r → intSeriesEval (expand p hp F) z = intSeriesEval F (z ^ p))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
