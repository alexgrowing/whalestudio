import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem poincare_well_defined (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) : PhWellDef X u hK :=
  phWellDef_of_steps X u hK hS hN

theorem poincare_properties (hK : X.LevelSubgroupCharacter) (hR : FoldReadyX X) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u)
    (hL : RatLevi X u) (hP : PsiProd X u) : PhProps X u hK :=
  phProps_of_steps X u hK (Formalism.L2.SG.Closed.level_subgroup_properties X) hR hS hN hL hP

theorem poincare_integral_finite (hK : X.LevelSubgroupCharacter) (hF : SratFund X u) (hM : MultPoly X) (hW : WuDecay.WuDecay X)
    (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) (hU : IUnfold X u hK) : IFinite X u hK :=
  iFinite_of X u hK hF hM hW (phWellDef_of_steps X u hK hS hN) hU

theorem poincare_in_holomorphic_space (hK : X.LevelSubgroupCharacter) (hR : FoldReadyX X) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u)
    (hL : RatLevi X u) (hP : PsiProd X u) (hW : WuDecay.WuDecay X) (hF : SratFund X u) (hM : MultPoly X)
    (hU : IUnfold X u hK) (hFB : FundBridge X) (hPM : PserMeas X u hK) (hRph : PserRph X u hK) (hPI : PhInt X)
    (hRF : ArchimedeanConvolutionFixesInvariantL2 X) (hEF : IdempotentFixesInvariantL2 X) : InHH X u hK :=
  inHH_of_steps X u hK (Formalism.L2.SG.Closed.level_subgroup_properties X) hR
    (@Formalism.L2.SG.Closed.fold_L2_first X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    (@Formalism.L2.SG.Closed.fold_L2_second X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf)
      (@muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar))
    hS hN hL hP hW hF hM hU hFB hPM hRph hPI hRF hEF

theorem poincare_linear (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) : PuLinear X u hK Dt := puLinear_holds X u hK Dt

theorem columns_link (hK : X.LevelSubgroupCharacter) (hC : BaseLevelSetClosed X u) (hF : GamFinOrd X u) (hU : GamUnip X u)
    (hCF : ClassFin X u hK) : ColsLink X u hK :=
  colsLink_of X u hK hC hF hU hCF

theorem foldReadyX_holds : FoldReadyX X := Formalism.L2.SG.Pf.foldReady_holds X.B.I

theorem sratFund_holds : SratFund X u := by
  obtain ⟨Fs, -, h⟩ := Formalism.L2.SG.Pf.exists_fund_srat_holds X u
  exact ⟨Fs, h _⟩

theorem phProps_closed (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) (hL : RatLevi X u)
    (hP : PsiProd X u) : PhProps X u hK :=
  poincare_properties X u hK (foldReadyX_holds X) hS hN hL hP

theorem iFinite_closed (hK : X.LevelSubgroupCharacter) (hM : MultPoly X) (hW : WuDecay.WuDecay X) (hS : KsetSplit X u)
    (hN : UnipotentConjugateInLevel X u) (hU : IUnfold X u hK) : IFinite X u hK :=
  poincare_integral_finite X u hK (sratFund_holds X u) hM hW hS hN hU

theorem inHH_closed (hK : X.LevelSubgroupCharacter) (hS : KsetSplit X u) (hN : UnipotentConjugateInLevel X u) (hL : RatLevi X u) (hP : PsiProd X u)
    (hW : WuDecay.WuDecay X) (hM : MultPoly X) (hU : IUnfold X u hK) (hFB : FundBridge X) (hPM : PserMeas X u hK)
    (hRph : PserRph X u hK) (hPI : PhInt X) (hRF : ArchimedeanConvolutionFixesInvariantL2 X) (hEF : IdempotentFixesInvariantL2 X) : InHH X u hK :=
  poincare_in_holomorphic_space X u hK (foldReadyX_holds X) hS hN hL hP hW (sratFund_holds X u) hM hU hFB hPM hRph hPI hRF hEF

end Formalism.L2.SG.PoincareInHH.Cut
