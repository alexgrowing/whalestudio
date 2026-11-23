import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.BotAsm
import Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
import Development.WeilBound.ThetaLifts.LatticeBasics.CoefLine
import Development.WeilBound.ThetaLifts.LatticeBasics.HermCpt
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerHalf
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInert
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplit
import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
import Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf
import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsFin
import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstFin
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
import Development.WeilBound.ThetaLifts.LatticeBasics.OrthAn
import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpen
import Development.WeilBound.ThetaLifts.LatticeBasics.HeightGLLe
import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitaryDensity.EqTopOfLines

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEst (GrpTop EpsOf SiegelAll FinVolU)
open PositivityTheory.ThKF (Unimod ArchOp ICont PureAct CartanConj CartanMove)

theorem _root_.PositivityTheory.ThKR.polynomial_vanishing_of_compactness (p0 : SiegelWeilStd) (p2 : EisBL) (p5 : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne)
    (hN : NonZeroAn) (hF : Factor) (hM : MatchEx) (hB : ThetaBasic) (hW : WeilConv) (hD : KDecay) (hI : ICont)
    (g1 : GrpTop) (g2 : EpsOf) (g3 : SiegelAll) (g4 : FinVolU) (g5 : Unimod) : PolZero :=
  have p1 := siegelWeilAniso_of p0 frameConj finLevel stab2Cpt
  have hc := cptAll_of g1 g2 g3 g4 g5
  have l1 := boxSec_of finLevel stab2Cpt
  have l6 := pairsStable
  polZero_of hc (hermLine_of' hc l6 pairsIrr hF hN hW hB hI hM)
    (coefLine_of (swFull_of p1.1 (eisContinues_of p2 frameConj) l1) l1 dblW (hgtEx_of stab2Cpt) (hgtInt_of stab2Cpt) stab2Cpt hc l6 hM
      hB hI polSch)
    (thConst_of' locDist goodNe (PositivityTheory.SA.constOfGood p5) hF hM hB hD g1 g2 g4 g5) hN hM hB hI polSch

end GlobalTheory.ThK.Dbl
