import Formalism.LocalToGlobal.GlobalTheory.GL4.ClassMapArchimedean
import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem slopeMaxGiven_free (D : D7) : SlopeMaxGiven D :=
  slopeMaxGiven_of_class D (slopeMaxClass_of_map D (class_map_of_archimedean D (class_map_archimedean D)))

theorem slope_inequality_constant_four (D : D7) : SlopeMaxOpenPart D 4 :=
  slope_bound_of_max_slope hookBound_holds D (slopeMaxGiven_free D)

theorem slope_inequality_family_four {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeMaxOpenPart Fm 4 := by
  unfold FamilySlopeMaxOpenPart fam0
  exact ⟨0, fun _ _ _ _ => slope_inequality_constant_four _⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
