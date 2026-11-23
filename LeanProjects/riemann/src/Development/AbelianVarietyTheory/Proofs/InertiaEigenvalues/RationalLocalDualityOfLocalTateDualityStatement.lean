import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLocalDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.RatIso := by
  first | exact @GlobalTheory.ratIso_of_localTateDuality | exact GlobalTheory.ratIso_of_localTateDuality | (intros; apply GlobalTheory.ratIso_of_localTateDuality <;> assumption)
