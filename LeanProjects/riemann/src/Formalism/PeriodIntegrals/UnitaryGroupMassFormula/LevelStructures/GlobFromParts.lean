import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem globFromParts_holds : GlobFromParts := by
  intro hLS h1 h2 h3 h4 D X hb _ _ w
  obtain ⟨hCM, hJ⟩ := h1 X
  obtain ⟨T, hT⟩ := h2 X w
  obtain ⟨ΛX, ΛW, ΛY, hA, hK⟩ := h3 X w
  obtain ⟨-, -, hHf, -, -, hNf, hSf, -⟩ := X.measW_norm w
  have key := (hLS X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hJ hJ D.R.rS (frameOf X w) T hT
    ΛX ΛW ΛY hA (X.measW w).μNf hNf (X.measW w).μHf hHf).2 (X.measW w).μSf ⟨hSf, h4 X w⟩
  simp only [KS, NO, KH, Subgroup.mem_inf, hK, SetLike.coe_mem, true_and] at key
  unfold muSf muNf muHf
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal key

end MassDataLevelSSteps
