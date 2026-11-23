import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.LinearIndependentFrameWithNormal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepGramH

noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

def StepFrameStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
  ∃ T : X.B.I.F, (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T

theorem stepGramH_of (h : StepFrameStd) : StepGramH := by
  unfold StepGramH
  intro D X u hT1
  obtain ⟨T, hT⟩ := h X u
  exact PI.VolNzeroOne.W.det_gram_tupH_ne_zero X.B.I.cm.sig X.B.I.J (frameOf X u) T hT hT1

end MassDataVolumesW
