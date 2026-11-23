import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
import Formalism.PeriodIntegrals.NUnimodLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Closed

theorem NUnimodLoc_holds : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  have h := n_unimodular_local
  intro k r ε e f wf z0 z c hF hc hz
  exact h k r ε e f wf z0 z c ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem QuotProdK_holds : Formalism.L2.SG.Pf.WFL.QuotProdK := quotient_product_compact

open Formalism.L2.SG.Pf.WFL in
variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] in

theorem setting_exists_of_gap (hPC : Formalism.L2.SG.Pf.LatEx.PrimesInClasses)
    (D : D7) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    ∃ X : Formalism.L2.SG.HidaSetting.HidaSetting D, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I, X.MeasTie hb := by
  obtain ⟨A⟩ := InstExists_holds D
  obtain ⟨L⟩ := LatExists_of_primesInClasses hPC D
  obtain ⟨P⟩ := PsiExists_holds D A
  obtain ⟨Rf⟩ := RefExists_holds D A L
  obtain ⟨Xu⟩ := XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := BunExists_holds D CoefWeightedLoc_holds hG A L P Rf
  obtain ⟨Pi⟩ := PiExists_holds D A L
  obtain ⟨Mu⟩ := MuExists_holds D A L
  obtain ⟨Wb⟩ := weighted_block_exists_of_local_data QuotProdK_holds locHNProps_holds NUnimodLoc_holds D BesselNVGap_holds
    CoefWeightedLoc_holds WlocExists_holds (GapBigOfGapHyp_holds D) hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := MExists_holds D A L P Rf Xu Bu Pi Mu Wb
  exact ⟨mk A L P Rf Xu Bu Pi Mu Wb Mb, hb, hM⟩

end Formalism.L2.SG.Closed
