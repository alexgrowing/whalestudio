import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.InVolumesAtOfSWW

noncomputable section

namespace PI.VolStabS.MassDataS

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Volumes
  Formalism.L2.SG.Measures Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory MassDataVolumesW

def SWXS : Prop := ∀ {D : D7} (X : HidaSetting D),
  Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧
    Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J

theorem volStabXS_of (hSW : SWXS) : ∀ {D : D7} (X : HidaSetting D),
    Formalism.L2.SG.Pf.NcWeil.VolStabW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J := fun X =>
  PI.VolStabS.Assembly.volStabFromSW_holds _ _ _ (stepCM X) _ _ (stepHerm X) (hSW X).1 (hSW X).2

theorem inVolumesAt_of_SWS (hSW : SWXS) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InVolumesAt X hb hK FdN FdN' u u' X0 L A :=
  inVolumesAt_of_w (volStabXS_of hSW) (stepGramH_of MassDataLevelSSteps.frameStd_holds)

end PI.VolStabS.MassDataS
