import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJUnram
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgClose
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

theorem cm2 (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt) : CM2 :=
  goodReduction_of_integral_unramified jInt (jUnram hH hC)

end ReciprocityTheory.ChartRestriction.L1
