import Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreExpansionZeroFails
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute

namespace Formalism.FourierDecayAlt.P

theorem big_cell_vanishing_differential (hJ : C6.JCommuteBig) : C6.BigCellVanishing :=
  big_cell_vanishing_of_commute' hJ

theorem vanishing_of_budget_and_density (hJ : C6.JCommuteBig) (hB : C6.BudgetClass) (hD : C6.LemmaDens) :
    C6.Vanishing :=
  vanishing_of_components_true (big_cell_vanishing_differential hJ) hB c6_budgetArith_proof big_cell_threshold hD

end Formalism.FourierDecayAlt.P
