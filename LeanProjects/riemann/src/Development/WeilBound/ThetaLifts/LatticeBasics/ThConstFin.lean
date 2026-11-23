import Development.WeilBound.ThetaLifts.LatticeBasics.ThConst
import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstSplit
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem thConst_of' (hL : LocDist) (hG : GoodNe) (hC : ConstOfGood) (hF : Factor) (hM : MatchEx) (hT : ThetaBasic) (hD : KDecay)
    (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : PositivityTheory.ThKEst.EpsOf) (h3 : PositivityTheory.ThKEst.FinVolU) (h4 : PositivityTheory.ThKF.Unimod) : ThConst :=
  thConst_of hL hG hC hF hM hT hD h1 h2 h3 h4 TC.splitModel PositivityTheory.KCo.so_statement

end GlobalTheory.ThK.Dbl

end
