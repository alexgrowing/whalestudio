import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBTheta

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LoopLoc

variable {D : D7}

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem wuBessel_of {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hJ : PI.BesselMapUniq.BesselMapUniq) (C : Choice X θ) : WuBessel C :=
  Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG (Formalism.MainNotions.BridgeCS3dBOW.besselOfW_of_jsz hJ)
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

def loopLocDatOf (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (hT : Formalism.BasicNotions.dsigTie D)
    (hJ : PI.BesselMapUniq.BesselMapUniq) {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) {large₂ : SizeData₂ D} {C1 : ℝ}
    (hwin : normWin D large₂ C1 θ) (u u' : D.what₂.Word) : Formalism.L2.SG.LoopTieOf.LoopLocDat D large₂ u u' C1 where
  θ := θ
  θ_win := hwin
  W τ := locW C u u' τ
  goodW τ := goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ)
    (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)
  A τ := locS (wuBessel_of hG hJ C) u u' τ
  goodS τ := goodS_of (wuBessel_of hG hJ C) u u' τ (Formalism.L2.SG.Pf.goodSRest_all hG hT (wuBessel_of hG hJ C) u u' τ)
  deg_eq τ := deg_eq (wuBessel_of hG hJ C) u u' τ

end Formalism.L2.SG.Pf.LoopLoc
