import Formalism.SharpRestriction.LevelLetterCocycles.SplitPolarLOf
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesAdmittedOfLevels
import Formalism.SharpRestriction.LevelLetterCocycles.PolarToPoleOfCtx

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem splitShapeL_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hArc : AdmArcA D HW F Cm) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (h9 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) : Split.SplitShapeL D HW :=
  Split.splitShapeL_of_pieces D HW (splitPolarL_of D HW F Cm hArc (arc_coordinates_of_levels D HW F Cm h1 h2) h23 h9)
    (Split.polarToPoleL_of D HW F Cm hArc)

end Formalism.MainNotions.UnusedSlot80
