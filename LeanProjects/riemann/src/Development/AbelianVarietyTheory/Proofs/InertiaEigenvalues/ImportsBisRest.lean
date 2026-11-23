import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrAAndNatural
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmHerrLocal

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F :=
  fun D HW F => Formalism.MainNotions.HerrComplexNaturality.herr_class_maps_of_naturality D HW F
    (Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_a_and_natural D HW F))
    (GlobalTheory.HerrExtUnit.main D HW F)

end GlobalTheory.AdmHerrLocal
