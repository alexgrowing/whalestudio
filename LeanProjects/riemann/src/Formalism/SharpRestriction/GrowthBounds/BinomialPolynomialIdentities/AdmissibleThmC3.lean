import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.ClosureThirdPart

noncomputable section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem admissible_thm_C3 (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BranchingColumnFamily D :=
  fun m _ M lam β hl hS => Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_third_part m (br_toC M) lam β hl hS

end Formalism.MainNotions.G.ColumnFamilies
