import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdMid
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnipotentBorelTuples.BorelTupU
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.TtSmul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.ThetaW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.KFinPolyOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOf

noncomputable section

open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem tWeyl_of (hP : TW.Poisson) : TWeyl :=
  TW.tWeyl_of TBij.tBij tTheta (TW.UpToPf.upTo_of TW.Twu.uniq) hP TW.ThetaWPf.thetaW

theorem siegelWeilStd_pre (hP : TW.Poisson) (hCT : CTSplit) : SiegelWeilStd :=
  have hT := tAll_of (tWeyl_of hP)
  siegelWeilStd_mid (tWeyl_of hP)
    (KFP.kFinPoly_of hT Tunit.tUnit Tunit.tHeis kfour.auxEx KFock.fockMem (locOpEx_of_tAll hT) (locInst_of hT))
    (Ald.ldEx_of hT kfour.auxEx) hCT

end PositivityTheory.SiegelWeilFormula.Fin

end
