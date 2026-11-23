import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.LocDecompOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConstOf
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst PositivityTheory.KCo

theorem splitB : SplitB := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t
  obtain ⟨⟨ι, hι⟩, -, h2, h3⟩ := dictionary_extended F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v t
  exact ⟨h2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (h3 ι hι).1 g hg _ rfl⟩, (h3 ι hι).2⟩

theorem sigThConst_fin (hB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) (hP : TriplePair) (hK : KDecay) (hF : SoFin)
    (hU : PositivityTheory.ThKF.Unimod) (hS : PolSch) (hN : GoodNe) (hC : ConstOfGood) (hL : LocDist)
    (h1 : KReal) (h2 : KFin) (h3 : KCoinv) : SigThConst :=
  sigThConst_of hP hN hC (locDecomp_of hB hE hU hP hK hF hS dictionary_statement hN h1 h2 h3) (pairLoc_of hB hE hV hU hL splitB) (thAut_of hB hG hE hV)

theorem orthIso_fin (hB : ThetaBasic) (hH : PositivityTheory.ThKG.Tow.PlaneHerm) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) (hA : SiegelAll)
    (hP : TriplePair) (hW : WeilConv) (hO : SoDecay) (hU : DomSoU) (hF : SoFin) (hS : PolSch) (hN : GoodNe)
    (h1 : SigRapid) (h2 : SigThConst) : OrthIso :=
  orthIso_of hB hP hW hU hF hS hN h1 h2 (thZero_of hB hE hV hA hO hF hH dictionary_statement) (thPerp_of hB hG hE hV)

end PositivityTheory.ThKEnd.Orth

end
