import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.AnaCore

noncomputable section

namespace PI.SqfPrimeFactor.W

theorem analytic_of (hRS : PI.PrimesDyadicRS.Claim) : Analytic := by
  intro g r hr hg
  refine ana_main hRS g r hr hg (bigPrimes r) (fun p => ?_)
  simp only [bigPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

end PI.SqfPrimeFactor.W
