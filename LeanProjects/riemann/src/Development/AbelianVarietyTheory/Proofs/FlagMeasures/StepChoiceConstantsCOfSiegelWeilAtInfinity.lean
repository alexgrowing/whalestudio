import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil

namespace GlobalTheory.St

theorem stepChoiceDataC_of_siegelWeil_inInfinity :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
    (∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word),
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.RealObj.InInfinityX X u u' 1) →
    Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC :=
  fun h hI => Formalism.L2.SG.Pf.choice_massData (GlobalTheory.St.swxs_of_siegelWeil h)
    Formalism.L2.SG.Pf.ProdConvCut2.prodConv_onTied hI

end GlobalTheory.St
