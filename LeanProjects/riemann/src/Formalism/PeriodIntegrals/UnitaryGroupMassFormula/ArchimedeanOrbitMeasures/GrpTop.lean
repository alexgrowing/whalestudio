import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UniInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW

noncomputable section

namespace PI.AprimeInfW

theorem grpDens_of_exp (hE : ExpProdU) : GrpDens :=
  grpDens_of (ginfDens_of (placeCharts_of (placeChartV_of hE))) unimodInf_holds

theorem grpStd_of_leaves (hE : ExpProdU) (hH : GrpHaarH) : GrpStd :=
  grpStd_of (grpPiecesStd_of blockEx_holds chiStab' (grpDens_of_exp hE) hH grpInj_holds)

theorem grpStd_of_exp_block (hE : ExpProdU) (hBH : BlockHaarV) : GrpStd :=
  grpStd_of_leaves hE (grpHaarH_of hBH)

end PI.AprimeInfW
