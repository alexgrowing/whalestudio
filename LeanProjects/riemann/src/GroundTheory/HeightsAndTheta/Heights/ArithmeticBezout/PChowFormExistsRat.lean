import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemConePointsSpanX0
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIntChowFormExists
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem ChowFormExistsRat.proof (hA : ObjectsChow.ChowFormToComplexChowForm.Statement)
    (hD : ObjectsChow.GenericFibreDim.Statement) : ChowFormExistsRat.Statement := by
  intro n e P hP
  have hQ := (ObjectsChow.GenericFibreIdeal.proof n (e + 1) P hP).1
  obtain ⟨g, hg⟩ := ObjectsChow.chowFormExists ℚ n (e + 1) (ObjectsChow.genericIdeal P) hQ
    (hD n (e + 1) P hP)
  obtain ⟨δ, -, hδ⟩ := ChowFormMultiHomog.full ℚ n (e + 1) (ObjectsChow.genericIdeal P) g hQ hg
  exact ⟨δ, g, hA n e δ P g hP hg hδ⟩

end GroundTheory.Heights₂.Heights
