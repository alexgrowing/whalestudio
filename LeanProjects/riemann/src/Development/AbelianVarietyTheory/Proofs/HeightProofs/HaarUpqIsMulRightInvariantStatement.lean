import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open MeasureTheory Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_upq_is_mul_right_invariant : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure <;> assumption)
