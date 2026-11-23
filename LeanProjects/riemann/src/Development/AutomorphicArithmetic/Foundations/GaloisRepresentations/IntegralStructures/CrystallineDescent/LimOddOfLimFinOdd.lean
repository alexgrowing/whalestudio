import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.IsoOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneUsHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.AutTHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PhiPol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.CsdLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.RamUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownDR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownCrys
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownPhi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinEndHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinAll
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.BadFinite
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ExistsQuadraticCMExtSplitAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.FirstQuadraticSquareHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

namespace UpperTheory.Gal.Int.Core

open UpperTheory.Gal.TP

theorem joinU_holds : JoinU :=
  joinU_of oneUs_holds isoOne_holds phiPol_holds autT_holds Sub.satAE_holds Sub.clConj Sub.satPol_holds Sub.clAway_holds

theorem subtractQ_holds : SubtractQ :=
  subtractQ_of Sub.charEx Sub.satAE_holds (Sub.denseId_holds Sub.cpFacts_holds Sub.dgFacts_holds) Sub.cpFacts_holds Sub.peelAll
    Sub.clTw Sub.contLeft_holds Sub.sSLeft_holds Sub.satPol_holds Sub.clConj

theorem joinAll_holds : JoinAll := joinAll_of oneUs_holds subtractQ_holds

theorem sphDown_holds : ∀ c, SphDown c
  | .unr => downUnr_holds
  | .dR => downDR_holds
  | .crys => downCrys_holds
  | .phi => downPhi_holds

theorem stepDown_holds : StepDown :=
  stepDown_of isoOne_holds (patchOne_holds isoOne_holds oneTower_holds oneConj_holds) sphDown_holds

theorem joinUp_holds : JoinUp := joinUp_of' stepDown_holds csdLift_holds ramUnr_holds oneUs_holds exists_quadratic_CM_ext_split_at

theorem rowCsd_of (hT : TwoUpOK) (hD : GlobalTheory.Cong.DescOffT) (hL : LimU) : RowCsd :=
  joinUp_holds PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity UpperTheory.Gal.AbelianGaloisNormality.gk_holds
    (GlobalTheory.QuadLiftBridge.quadLift UpperTheory.Gal.AbelianGaloisNormality.strongTC_holds PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity)
    (joinGL_holds hD (joinAll_holds hT (joinU_holds hL)))

theorem core_of_limU (hT : TwoUpOK) (hD : GlobalTheory.Cong.DescOffT) (hL : LimU) : GlobalTheory.RoadU.Core :=
  GlobalTheory.RoadW.core_of_rowStarCore (joinEnd_holds (rowCsd_of hT hD hL))

theorem core_of_limOdd (hT : TwoUpOK) (hC : GlobalTheory.CongPhi.ClosedPhi) (hD : GlobalTheory.Cong.DescOffT) (hL : LimOdd) : GlobalTheory.RoadU.Core :=
  core_of_limU hT hD (limU_of_limOdd hC hL)

theorem limOdd_of_limFinOdd (h : GlobalTheory.CongL.LimFinOdd) : LimOdd := fun E Ω _ _ _ _ _ _ l _ ι a ha => h E Ω l ι a ha.pos ha

theorem toCore (hT : TwoUpOK) : GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  fun hC hD hL => core_of_limOdd hT hC hD (limOdd_of_limFinOdd hL)

end UpperTheory.Gal.Int.Core
