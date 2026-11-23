import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureFiniteInvariant
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianNormFibreMeasure_finite_invariant : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β : ℝ), IsDxDq fib → β ≠ 0 → IsFiniteMeasureOnCompacts (fib β) ∧ ∀ g : UpqT P Q, (fib β).map (act g) = fib β := by
  first | exact @GlobalTheory.FibreInvariance.fibre_finite_invariant | exact GlobalTheory.FibreInvariance.fibre_finite_invariant | (intros; apply GlobalTheory.FibreInvariance.fibre_finite_invariant <;> assumption)
