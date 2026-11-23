import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory

def CovolumeRelIndex.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁]
    [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂], L₁ ≤ L₂ →
      ZLattice.covolume L₁ μ = (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ

abbrev CovolumeRelIndex.stdLattice : Submodule ℤ (Fin 1 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1)))

end GroundTheory.Heights₂.Heights.Targets
