import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds

noncomputable section

namespace PI.AprimeInfW

theorem properOrb_of_compact (hH : MassDataMassesW.HinfCompact) : ProperOrb :=
  properOrb_of_one (properOne_of wittInf_holds hH) invNbhd_holds

theorem pushCont_of_compact (hH : MassDataMassesW.HinfCompact) : PushCont :=
  pushCont_of frame_independent_at_infinity (properOrb_of_compact hH)

theorem pushLFin_of_compact (hH : MassDataMassesW.HinfCompact) : PushLFin :=
  pushLFin_of_proper (properOrb_of_compact hH)

theorem constTest_of_polar_compact (hP : PolarLoc) (hH : MassDataMassesW.HinfCompact) : ConstTest :=
  constTest_of_polar hP (pushCont_of_compact hH)

end PI.AprimeInfW
