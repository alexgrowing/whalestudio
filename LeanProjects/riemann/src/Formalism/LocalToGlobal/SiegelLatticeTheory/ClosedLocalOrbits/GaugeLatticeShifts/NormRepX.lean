import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.StarSqrtMinusD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.Pf.NormRepX

theorem norm_representative_holds (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word)
    (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) : Formalism.L2.SG.Pf.NormRepStep D u u' :=
  PI.NRL.normRepStep_of_trace D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') hP (Or.inr (PI.NRL.traceOne D))

end Formalism.L2.SG.Pf.NormRepX
