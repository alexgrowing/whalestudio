import Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv
import Development.WeilBound.ThetaLifts.FrameEstimates.OneMemLines
import Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
import Development.WeilBound.ThetaLifts.FrameEstimates.IInvOfParts
import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
import Development.WeilBound.ThetaLifts.FrameEstimates.UMGLin
import Development.WeilBound.ThetaLifts.FrameEstimates.UMGSmooth
import Development.WeilBound.ThetaLifts.FrameEstimates.LinDer
import Development.WeilBound.ThetaLifts.FrameEstimates.LineGen
import Development.WeilBound.ThetaLifts.FrameEstimates.LineEx
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapidOf
import Development.WeilBound.ThetaLifts.FrameEstimates.SigRapid

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem umgSmooth : UMGSmooth := umgSmooth_of (linDer_of lineGen_of lineEx_of) lineGen_of

theorem cuspRapid (h : GlobalTheory.Published.SiegelSetUnitary) : CuspRapid := cuspRapid_of h umgSmooth

theorem level : Level := level_of coefEq_of fourierInj_of (coefBd_of coefReal_of)

theorem iDer (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IDer := iDer_of hB hO hL (iInv_of hB)

theorem iUMG (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IUMG :=
  iUMG_of hB grpTop_of epsOf_of (iDer hB hO hL) level (iInv_of hB)

theorem sigRapid (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) :
    PositivityTheory.ThKEnd.Orth.SigRapid :=
  sigRapid_of hB umgLin_of epsOf_of (iUMG hB hO hL) (iInv_of hB) Sq.triplePair_holds (domWeil_of_U (domWeilU h)) (domSoU h)
    soFin_of (cuspRapid h)

end PositivityTheory.ThKEst

end
