import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ClauseUnique
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AinfValueOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GinfTestHolds

namespace PI.AprimeInfW

theorem aprimeInf_iff : Formalism.L2.SG.Pf.NcReal.AprimeInf ↔ AprimeInfS := Iff.rfl

theorem aprimeInf_of (hV : AinfValue) (hG : GinfTest) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_iff.2 (aprimeInfS_of hV hG)

theorem aprimeInf_of_steps (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hH : HtotInf) (hG : GinfTest) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of (ainfValue_of hE hP hW hH) hG

theorem aprimeInf_of_open (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hF : HinfFin) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_steps hE hP hW (htotInf_of hF) ginfTest_holds

theorem aprimeInf_of_leaves (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hC : MassDataMassesW.HinfCompact) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_open hE hP hW (hinfFin_of hC)

end PI.AprimeInfW
