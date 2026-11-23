import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

def LatticeCountVolume.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La]
    [IsZLattice ℝ La] (S T : Set E), MeasurableSet S → (∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) →
      μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume La μ)

abbrev LatticeCountVolume.stdLattice : Submodule ℤ (Fin 1 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1)))

end GroundTheory.Heights₂.Heights.Targets
