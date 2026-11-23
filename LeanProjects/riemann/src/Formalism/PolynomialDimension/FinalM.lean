import Formalism.MahlerMeasure.FinalT
import Formalism.MahlerMeasure.MahlerMeasureProofs.WeightSpaceDimensionMonotone
import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
import Formalism.PolynomialDimension.MultinomialDepth.MonoCount
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.PolynomialDimension.MultinomialDepth.TieOps

namespace Formalism.CountingSumsFrames.Top
open Formalism.GM

theorem partnerM_of_tieOps (h : Formalism.CountingSumsFrames.TieOps) : TM.PartnerM := Formalism.CountingSumsFrames.partnerM_of_tieOps h

theorem theoremM_of_tieOps (h : Formalism.CountingSumsFrames.TieOps) : M.TheoremM :=
  theoremM_of_partner Formalism.GM.Top.meanGam Formalism.GM.weight_space_dimension_monotone Formalism.CountingSumsFrames.monomial_count Formalism.GM.Top.badCrit
    Formalism.GM.smith_form_p_adic_integers (Formalism.CountingSumsFrames.partnerM_of_tieOps h)

theorem theoremM : M.TheoremM := theoremM_of_tieOps Formalism.CountingSumsFrames.level_operators_exist

end Formalism.CountingSumsFrames.Top
