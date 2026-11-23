import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryExpLieBallComparableEntryGauge
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryExpLieBall_comparable_entryGauge : ∀ (P Q : ℕ) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), expBall P Q (t⁻¹ * r) ⊆ {g : UpqT P Q | gauge g < r} ∧ {g : UpqT P Q | gauge g < r} ⊆ expBall P Q (t * r) := by
  first | exact @GlobalTheory.ExpBallCompare.expBall_compare | exact GlobalTheory.ExpBallCompare.expBall_compare | (intros; apply GlobalTheory.ExpBallCompare.expBall_compare <;> assumption)
