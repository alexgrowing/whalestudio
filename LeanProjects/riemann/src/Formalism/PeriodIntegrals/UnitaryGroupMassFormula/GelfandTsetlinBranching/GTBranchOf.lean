import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionD

noncomputable section

namespace PI.WGB

theorem gTBranch_of (h : PI.HwIrred) : PI.GTBranch :=
  gTBranch_of_steps h (extremalFacts_of h) fixed_line_exists stable_complement_exists highest_weight_vector_exists
    (realize_of h (extremalFacts_of h) fixed_line_exists stable_complement_exists highest_weight_vector_exists)

end PI.WGB
