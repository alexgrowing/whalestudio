import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.WindowBoundOddCases
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.FiltrationGenericPointCriterion

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B3
theorem admissible_thm_B1 (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.admB3 D :=
  fun n _ M CF => Formalism.InvariantFactorPaths.ColumnFamilies.filtration_theorem_one_of Formalism.InvariantFactorPaths.ColumnFamilies.Top.lemmaA n (br_toC M) (br_cfToC CF)
end B3

section B5
theorem admissible_thm_B3 (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GenericProjectionCriterion D :=
  fun n _ M CF => Formalism.InvariantFactorPaths.ColumnFamilies.filtration_criterion_of Formalism.InvariantFactorPaths.ColumnFamilies.Top.lemmaA n (br_toC M) (br_cfToC CF)
end B5

end Formalism.MainNotions.G.ColumnFamilies
