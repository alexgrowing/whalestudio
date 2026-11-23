import Formalism.LatticeSlopes.Statement

namespace Formalism.F

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_of_le {L N : Submodule ℤ E} (h : N ≤ L) [hL : DiscreteTopology L] :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (f := Submodule.inclusion h)
    (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective h)

end Formalism.F
