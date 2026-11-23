import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem killer_first_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C : ℝ} (hC : 8 ≤ C) :
    KillerWithConstantTheorem D HW F C := by
  intro hA
  obtain ⟨hL, hP⟩ := hA
  exact Formalism.MainNotions.ArcLiftingSetup.pi_stability_content_clause D HW F hC hL (fun l _ K LL hG hc h5 =>
    hP l K LL hc h5 ((HW l).W K 1 LL hG).gam)

theorem killer_second_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : KillerWachCoordinatesTheorem D HW F := by
  intro hP
  exact Formalism.MainNotions.WachCoordinates.killer_conditions_of_stable D HW F hP

theorem root_multiplicity_two (D : D7) : RootMultiplicityTwo D :=
  Formalism.MainNotions.ArcLiftingSetup.content_divisibility_clause D

end Formalism.MainNotions.UnusedSlot80
