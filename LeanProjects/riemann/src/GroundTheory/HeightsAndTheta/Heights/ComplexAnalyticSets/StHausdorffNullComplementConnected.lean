import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory

def HausdorffNullComplementConnected.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (D C : Set E),
    IsOpen D → IsPreconnected D → μH[(Module.finrank ℝ E : ℝ) - 1] C = 0 → IsPreconnected (D \ C)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
