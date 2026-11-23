import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdxGlobOfFinProj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S (AutInst)

theorem finProjOpen_holds : FinProjOpen := by
  intro I
  obtain ⟨e, he⟩ := MassDataMassesW.splitIso_holds I.cm.sig I.J
  have h : (fun h : HAd I => (splitA I.cm.sig I.J h).2) = Prod.snd ∘ e := by
    funext h
    simp only [Function.comp, he]
  rw [h]
  exact isOpenMap_snd.comp e.toHomeomorph.isOpenMap

end MassDataLevelSSteps
