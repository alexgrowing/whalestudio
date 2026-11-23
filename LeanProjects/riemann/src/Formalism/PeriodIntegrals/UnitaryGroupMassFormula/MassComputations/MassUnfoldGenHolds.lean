import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Unfold

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massUnfoldGen_holds : PIW.MassDataColumns.MassUnfoldGen := by
  intro D X u hM _ U _ hUo hfin 𝓕 h𝓕
  exact massUnfold_gen (hCM := isCMExt_of_cmData X.B.I.cm) (hJ := isHermND_of_setting X) (M := X.measW u)
    (hM := hM) (U := U) (hU := hUo.measurableSet) (hfin := hfin) (𝓕 := 𝓕) (h𝓕 := h𝓕)

end MassDataMassesW
