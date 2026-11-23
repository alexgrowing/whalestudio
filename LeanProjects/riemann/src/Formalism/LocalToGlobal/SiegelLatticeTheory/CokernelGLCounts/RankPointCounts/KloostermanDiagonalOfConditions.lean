import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairsDegCutCOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDimensionFormula

noncomputable section

open Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal

namespace Formalism.L2.SG.KappaOffDiagonal

theorem corankPosC_holds : Formalism.L2.SG.RowsConc.CorankPosC :=
  fun _ _ Y u u' _ => Formalism.L2.SG.Pf.SatGram.corankPos_tO Y u u'

theorem pairsDegree_of_conditions (hFold : FoldOKC) (hOI : OOIntAllC) (hIV : IrrVecC) (hJP : JPosC) (hTy : TypeC) (hDl : DelC)
    (hDim : DimFormC) : Formalism.L2.SG.RowsConc.PairsDegCutC :=
  pairsDegCutC_of_steps hFold Formalism.L2.SG.Pf.fundExistsC_holds hOI hIV hJP hTy hDl hDim
    Formalism.L2.SG.Pf.splitPrimeLoc_holds Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds

theorem kloostermanDiagonal_of_conditions (hFold : FoldOKC) (hOI : OOIntAllC) (hIV : IrrVecC) (hJP : JPosC) (hTy : TypeC) (hDl : DelC)
    (hDim : DimFormC) (hN : Formalism.L2.SG.RowsConc.NormExpDegC) : Formalism.L2.SG.RowsConc.KppDiagC :=
  Formalism.L2.SG.RowsConc.kppDiagC_of_cut Formalism.FourierDecayAlt.P.price_of_index Formalism.FourierDecayAlt.P.equal_index
    Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.L2.SG.Closed.TermsGGBound_holds corankPosC_holds hN
    (pairsDegree_of_conditions hFold hOI hIV hJP hTy hDl hDim)

theorem kloostermanDiagonal_of_typeCond (hFold : FoldOKC) (hOI : OOIntAllC) (hIV : IrrVecC) (hJP : JPosC) (hTy : TypeC) (hDl : DelC)
    (hN : Formalism.L2.SG.RowsConc.NormExpDegC) : Formalism.L2.SG.RowsConc.KppDiagC :=
  kloostermanDiagonal_of_conditions hFold hOI hIV hJP hTy hDl kappa_off_diagonal_dim_form_C hN

end Formalism.L2.SG.KappaOffDiagonal
