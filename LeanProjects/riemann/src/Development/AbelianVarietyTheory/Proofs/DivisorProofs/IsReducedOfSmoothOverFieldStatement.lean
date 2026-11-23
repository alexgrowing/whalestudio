import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverField
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_smooth_over_field' : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A], IsReduced A := by
  first | exact @GlobalTheory.isReduced_of_smooth_over_field | exact GlobalTheory.isReduced_of_smooth_over_field | (intros; apply GlobalTheory.isReduced_of_smooth_over_field <;> assumption)
