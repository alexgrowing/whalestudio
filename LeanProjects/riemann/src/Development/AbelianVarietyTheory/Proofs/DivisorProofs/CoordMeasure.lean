import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.ParabolicCoord

def coordMeasure {G K T : Type} [Group G] [MeasurableSpace G] [Group K] [MeasurableSpace K]
    [CommGroup T] [MeasurableSpace T] (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0)
    (μQ : Measure Q) (μT : Measure T) (μK : Measure K) : Measure G :=
  (μK.prod ((μT.withDensity fun t => ((δ t : ℝ≥0) : ℝ≥0∞)).prod μQ)).map
    fun p => (p.2.2 : G) * (m p.2.1)⁻¹ * κ p.1

end GlobalTheory.ParabolicCoord
