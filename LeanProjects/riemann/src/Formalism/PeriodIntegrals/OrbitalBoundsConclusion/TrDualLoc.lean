import Formalism.PeriodIntegrals.TrDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceDualLocal.Imports

theorem trace_dual_local : PI.TrDualLoc.Stmt := by
  intro K _ _ p _ Fp _ _ _ _ _ hc hfin ι hd _ t ht c hcO
  haveI : CharZero Fp :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp).injective
  exact PI.TrDualLocW.main hc hfin ι (PI.CntNotIntW.tensorLiftSurjective K _ Fp hc hfin ι hd) t ht c hcO
