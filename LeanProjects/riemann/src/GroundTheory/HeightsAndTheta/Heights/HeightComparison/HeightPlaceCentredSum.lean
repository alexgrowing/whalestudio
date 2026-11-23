import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def PlaceCentredSum.Statement : Prop :=
  ∀ (L K : Type) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
    (O : Subalgebra ℤ L) (m : Ideal O) (t : L),
    ∑ᶠ v ∈ {v : FinitePlace K | AbsCentredAt O m fun u ↦ v (algebraMap L K u)},
        -Real.log (v (algebraMap L K t)) =
      Module.finrank L K *
        ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun u ↦ w u}, -Real.log (w t)

example : NumberField ℚ ∧ NumberField (CyclotomicField 4 ℚ) := ⟨inferInstance, inferInstance⟩

end GroundTheory.Heights₂.Heights
