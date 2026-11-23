import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

def CMInst : Prop :=
  ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J

def FrameStd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ T : X.B.I.F,
    (frameOf X w).IsStd X.B.I.cm.sig X.B.I.J T

def LatAdapted : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ ΛX ΛW ΛY : Set (Fin X.B.I.n → X.B.I.E),
    Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) ΛX ΛW ΛY ∧
    Kf X.B.I.cm.sig X.B.I.J (ΛX ∪ ΛW ∪ ΛY) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def ProdNH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word),
    IsProdNH X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (X.measW w).μSf (X.measW w).μNf (X.measW w).μHf

def GlobFromParts : Prop := LevelSAll → CMInst → FrameStd → LatAdapted → ProdNH → GlobLevelS

end MassDataLevelSSteps
