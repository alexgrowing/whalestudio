import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepGramH

noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem stepCM : StepCM := by
  intro D X
  exact ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

theorem stepHerm : StepHerm := by
  intro D X
  exact ⟨fun i j => congrFun (congrFun X.B.I.J_herm i) j, X.B.I.J_det⟩

end MassDataVolumesW
