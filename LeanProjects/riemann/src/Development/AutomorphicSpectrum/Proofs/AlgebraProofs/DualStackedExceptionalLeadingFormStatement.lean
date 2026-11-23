import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingForm
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_leading_form : GroundTheory.Heights₂.Heights.DualStackedExcLeadForm.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | exact GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm <;> assumption)
