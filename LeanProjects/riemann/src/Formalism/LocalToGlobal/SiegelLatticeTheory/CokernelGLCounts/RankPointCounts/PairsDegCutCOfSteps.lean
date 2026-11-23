import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanTermANonneg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo

noncomputable section

open Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

theorem pairsDegCutC_of_steps (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC)
    (hIV : IrrVecC) (hJP : JPosC) (hTy : TypeC) (hDl : DelC) (hDim : DimFormC)
    (hS : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc) (hRC : Formalism.L2.SG.Pf.SatGramLoc.RedCore) :
    Formalism.L2.SG.RowsConc.PairsDegCutC :=
  pairsDegCutC_of_cut hFold hFE hOI hIV hJP hTy hDl cosetsC_holds hDim (PgLe.pgLeC_of hS hRC)

end Formalism.L2.SG.KappaOffDiagonal
