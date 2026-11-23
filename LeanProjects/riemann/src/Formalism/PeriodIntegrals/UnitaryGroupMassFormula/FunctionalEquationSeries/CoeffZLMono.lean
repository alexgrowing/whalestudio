import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FunctionalEquationSeries.Development

noncomputable section

open MvPowerSeries

namespace PI.FunEqAllProof

open PI.FunEqAll

section

variable (l d : ℕ) [Fact l.Prime]

def mono (s : ZMod d) (e : ℕ) : ZMod d × Unit →₀ ℕ :=
  Finsupp.single (s - 2 * (e : ZMod d), ()) ((l ^ 2) ^ e)

end

end PI.FunEqAllProof
