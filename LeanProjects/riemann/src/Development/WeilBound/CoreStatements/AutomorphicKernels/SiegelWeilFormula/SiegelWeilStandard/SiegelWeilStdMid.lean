import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GoodSigPq
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.PolyKFinOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.GIdilFull
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.BorelTup
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadB

noncomputable section

open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem locInst_of (hT : TAll) : LocInst := KLI.locInst_of hT kfour.auxEx KFock.fockMem (KFock.liftEx hT.1)

theorem siegelWeilStd_mid (hW : TWeyl) (hKP : KFinPoly) (hLD : LDEx) (hCT : CTSplit) : SiegelWeilStd :=
  have hT := tAll_of hW
  siegelWeilStd_of hT (locInst_of hT)
    (Kdil.gIdil_full hT kfour.auxEx (locOpEx_of_tAll hT) (KAway.awayAct_of_tAll hT) (locInst_of hT)) hKP
    (KK.polyKFin_of hT KFock.fockMem) hLD hCT HSt.holLeadB

end PositivityTheory.SiegelWeilFormula.Fin

end
