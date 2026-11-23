import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.TransferStep

noncomputable section

namespace PI.UConjT

theorem conjTranspose_of (h1 : OnbReal) (h2 : TransferStep) (h3 : BlockStep) :
    PI.UMultOne.ConjTranspose := h3 (h2 h1)

end PI.UConjT
