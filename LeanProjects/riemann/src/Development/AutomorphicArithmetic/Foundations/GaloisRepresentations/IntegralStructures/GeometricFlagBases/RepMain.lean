import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagBasis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGrHom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PSSOfSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.EqZeroOfLowBlk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PContGL
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHopGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PPieceStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PRelDim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCompSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtotFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PStabOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PExtCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PTotCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.VFinOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepAsm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds

namespace UpperTheory.Gal.Int.Geo

theorem bcSplits : G3.BcSplits := G3.pBcSplits (G3.pSplitsBasic (G3.pSplitsPts G3.pIsoPts) G3.pPtsOfSplits)

theorem etGood : G3.EtGood := G3.pEtGood (G3.pEtnGood (G3.pFEtBasic G3.pPtsOfSplits) G3.pEtTr)

theorem galClos : G3.GalClos := G3.pGalClos (G3.pGalClosD (G3.pSplitsPts G3.pIsoPts) (G3.pOrdEx G3.pOrdStep))

theorem hopSpec : G3.HopSpec := G3.pHopSpec etGood (G3.pBcGood bcSplits (G3.pBcGal bcSplits)) galClos (G3.pOpEx G3.pOpTr)
  G3.pOpTr G3.pOpEt (G3.pOpBc bcSplits (G3.pBcGal bcSplits)) bcSplits

theorem grEx : GrEx := grEx_of flagEx_of flagBasis_of flagMove_of grHom_of (grSS_of grHom_of sSOfSum_of)

theorem hopGal : HopGal := hopGal_of hopSpec opConj_of (opUniq_of hopSpec (G3.pOpEx G3.pOpTr) G3.pOpEt etGood bcSplits)

theorem pieceStab : PieceStab := pieceStab_of hopGal

theorem degFin (h : KunnethLefschetz.Core) : DegFin :=
  degFin_of h.qDual KunnethLefschetz.inSum_holds h.inputs.a9 KunnethLefschetz.projBC_holds KunnethLefschetz.sumCl_holds KunnethLefschetz.sumHl_holds KunnethLefschetz.piBC_holds relDim_of compSum_of

theorem htotFin (h : KunnethLefschetz.Core) : HtotFin := htotFin_of (degFin h)

theorem degCont : DegCont := degCont_of (stabOpen_of htDesc_of)

theorem totCont (h : KunnethLefschetz.Core) : TotCont := totCont_of (vFin_of h.inputs) degCont

theorem repEx_core (h : KunnethLefschetz.Core) : RepEx :=
  repEx_of grEx contGL_of matEx_of matConj_of pieceStab (htotFin h) extCont_of (totCont h) KunnethLefschetz.projBC_holds

theorem repEx_holds : RepEx := repEx_core KunnethLefschetz.core_holds

end UpperTheory.Gal.Int.Geo
