import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

theorem claim_of (hA : CountA) (hB : IrrLower) (hC : Analytic) : PI.SqfPrimeFactor.Claim := by
  intro g r _ hr hg T hT
  refine (hA g r T hT).trans (le_trans ?_ (hC g r hr hg))
  gcongr with p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [div_le_iff₀ hp0]
  have := hB g p hpp
  linarith

end PI.SqfPrimeFactor.W
