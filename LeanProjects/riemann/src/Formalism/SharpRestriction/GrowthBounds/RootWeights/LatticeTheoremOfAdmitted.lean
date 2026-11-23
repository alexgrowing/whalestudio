import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorTraceFormula

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem lattice_theorem_of_admitted (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) : IsotypicProjectorTheoremField D :=
  isotypicProjectorTheoremField_of_sharp_bound D h2 (invariant_denominator_sharp_of D h2 h5)

end Formalism.MainNotions.G.GLWeightTheory
