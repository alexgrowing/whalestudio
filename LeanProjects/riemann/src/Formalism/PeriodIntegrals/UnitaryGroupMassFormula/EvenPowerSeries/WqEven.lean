import Formalism.PeriodIntegrals.PhEven

noncomputable section

namespace PI.PhEven.ParB

open PI.AddIntG

section Field

variable {K : Type*} [Field K]

def nu (K : Type*) [Field K] : PowerSeries K →+* PowerSeries K := PowerSeries.rescale (-1 : K)

end Field

variable {p : ℕ} [Fact p.Prime]

end PI.PhEven.ParB

namespace PI.PhEven

end PI.PhEven

end
