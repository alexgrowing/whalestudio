import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsWellDefined
import GroundTheory.HeightsAndTheta.Heights.Intersections.ThmIExistsFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ThmIExists

theorem ThmIExists.proof (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement) (hWD : WellDefined.Statement)
    (hSymm : ThmISymm.Statement) : ThmIExists.Statement := by
  refine ⟨fun K _ ι _ => famI (K := K) (ι := ι), fun K _ ι _ => ?_⟩
  have hRF : IsRFamily (famI (K := K) (ι := ι)) :=
    isRFamily_famI hD1 hMul fun n hR hA P L B s t hP hL hB hs ht =>
      hWD K ι famI P n L B s t hR hA hP hL hB hs ht
  exact ⟨hSymm K ι _ hRF, hRF.1, hRF.2⟩

end GroundTheory.Heights₂.Heights.Inter
