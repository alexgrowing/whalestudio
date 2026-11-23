import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Interface
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedModel
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormWeierstrassCoeffSmallJ
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Norm1728EqOneOfFiveLe

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem goodReduction_of_integral_unramified (hI : JInt) (hU : JUnram) : CM2 := by
  intro d L hsq hd4 hCM l _ h5 hld ι
  have hJ := hU d L hsq hd4 hCM l h5 hld ι
  have hJ1 := hI d L hsq hd4 hCM l ι
  exact model_of_valDiv L l h5 ι hJ hJ1 (valDiv3 d L hsq hd4 hCM l h5 hld ι hJ hJ1)
    (valDiv2 d L hsq hd4 hCM l h5 hld ι hJ hJ1)

end ReciprocityTheory.ChartRestriction.L1
