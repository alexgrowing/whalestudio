import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

def MixedBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F)) [DiscreteTopology La]
    [IsZLattice ℝ (E := mixedSpace F) La] (f : InfinitePlace F → ℝ), (∀ w, 0 < f w) →
      {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite ∧
        Real.log (convexBodyLTFactor F : ℝ) + ∑ w, (mult w : ℝ) * Real.log (f w) -
            Module.finrank ℚ F * Real.log 2 - Real.log (ZLattice.covolume La) ≤
          Real.log ({y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.ncard : ℝ)

end GroundTheory.Heights₂.Heights.Targets
