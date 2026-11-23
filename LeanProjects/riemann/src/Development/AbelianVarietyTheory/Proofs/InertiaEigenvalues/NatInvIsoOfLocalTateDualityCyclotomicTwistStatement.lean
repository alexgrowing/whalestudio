import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwist
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.NatInvIso := by
  first | exact @GlobalTheory.natInvIso_of_localTateDuality | exact GlobalTheory.natInvIso_of_localTateDuality | (intros; apply GlobalTheory.natInvIso_of_localTateDuality <;> assumption)
