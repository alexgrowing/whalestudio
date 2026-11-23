import Mathlib

universe u

open NumberField Module

namespace HeckeCharacterZeroLocus.ClassNumberQuad

def ClassNumberLe : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], finrank ℚ K = 2 → IsTotallyComplex K →
    (classNumber K : ℝ) ≤ Real.sqrt (|discr K| : ℝ) * (Real.log (|discr K| : ℝ) + 2) / Real.pi

end HeckeCharacterZeroLocus.ClassNumberQuad
