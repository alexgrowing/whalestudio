import Development.WeilBound.ThetaLifts.FrameEstimates.DomWeil
import Development.WeilBound.ThetaLifts.FrameEstimates.SoSemi
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.FrameEstimates.IContOf
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
import Development.WeilBound.ThetaLifts.FrameEstimates.SqAllC
import Development.WeilBound.ThetaLifts.FrameEstimates.ThetaSumNeg
import Development.WeilBound.ThetaLifts.FrameEstimates.HermitianFormDetNeZero
import Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
import Development.WeilBound.ThetaLifts.FrameEstimates.Parity
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefSum
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
import Development.WeilBound.ThetaLifts.FrameEstimates.LatInv
import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
import Development.WeilBound.ThetaLifts.FrameEstimates.LatCpt
import Development.WeilBound.ThetaLifts.FrameEstimates.LatArch
import Development.WeilBound.ThetaLifts.FrameEstimates.LatTor
import Development.WeilBound.ThetaLifts.FrameEstimates.LatFull
import Development.WeilBound.ThetaLifts.FrameEstimates.ExistsColsDetNeZero
import Development.WeilBound.ThetaLifts.FrameEstimates.OneVar
import Development.WeilBound.ThetaLifts.FrameEstimates.FrameBasis
import Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.TriplePairHolds

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sqAll : SqAll := sqAll_of' coefSum coefEq_of (coefBd_of coefReal_of)

theorem sqSo : SqSo :=
  sqSo_of' soFin_of soCut_of (parity_of coefEq_of fourierInj_of) coefSum coefEq_of (coefBd_of coefReal_of)

theorem latTor : LatTor := latTor_of frameBasis_of oneVar_of

theorem latFull : LatFull := latFull_of latTor (minor_of frameBasis_of)

theorem domWeilU (h : GlobalTheory.Published.SiegelSetUnitary) : DomWeilU :=
  domWeilU_of grpTop_of epsOf_of (siegelAll_of h) sqAll latInv_of latMeas latCpt_of (latArch_of frameBasis_of) latTor
    Sq.posWt' Sq.square_integrable_integral_holds

theorem soSemiU (h : GlobalTheory.Published.SiegelSetUnitary) : SoSemiU :=
  soSemiU_of grpTop_of epsOf_of (siegelAll_of h) sqSo latInv_of latCpt_of latFull Sq.posWt'

theorem domSoU (h : GlobalTheory.Published.SiegelSetUnitary) : DomSoU := domSoU_of epsOf_of finVolU (soSemiU h)

theorem weilConv (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : WeilConv :=
  weilConv_of hB (domWeil_of_U (domWeilU h)) soFin_of

theorem soDecay (h : GlobalTheory.Published.SiegelSetUnitary) : SoDecay := soDecay_of (soSemi_of_U (soSemiU h)) soFin_of

theorem soCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : SoCont := soCont_of hB (domSoU h) soFin_of

theorem kDecay (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : KDecay :=
  kDecay_of hB Sq.triplePair_holds (weilConv h hB) (soDecay h) (domSoU h) soFin_of

theorem sqInt (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : SqInt :=
  Sq.sqInt_of_leaves hB grpTop_of epsOf_of (siegelAll_of h) sqAll sqSo soFin_of latCpt_of latTor latFull

theorem iCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : PositivityTheory.ThKF.ICont :=
  iCont_of hB grpTop_of epsOf_of (domWeil_of_U (domWeilU h)) (domSoU h) soFin_of

end PositivityTheory.ThKEst

end
