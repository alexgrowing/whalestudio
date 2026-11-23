import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdPre
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntEqFour

open GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem siegelWeilStd_of_ct (hCT : CTSplit) : SiegelWeilStd := siegelWeilStd_pre TW.Twp.poisson hCT

end PositivityTheory.SiegelWeilFormula.Fin
