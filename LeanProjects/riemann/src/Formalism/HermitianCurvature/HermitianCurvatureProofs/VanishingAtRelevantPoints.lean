import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingDifferential
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetClassEstimate

namespace Formalism.FourierDecayAlt.P

theorem vanishing_at_relevant_points (hJ : C6.JCommuteBig) (hD : C6.LemmaDens) : C6.Vanishing :=
  vanishing_of_budget_and_density hJ budget_class_estimate hD

end Formalism.FourierDecayAlt.P
