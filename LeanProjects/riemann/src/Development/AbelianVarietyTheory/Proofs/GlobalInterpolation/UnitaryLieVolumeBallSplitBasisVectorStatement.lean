import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryLieVolumeBallSplitBasisVector
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLie_volume_ball_split_basis_vector : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ (lam : Measure (lieU P Q)) (lam' : Measure (lieU P' Q')), IsOmegaLeb lam → IsOmegaLeb lam' → ∀ r : ℝ, lam (ballU P Q r) = (2 : ℝ≥0∞) ^ (P' + Q') * ((volume : Measure (ℝ × Sp P' Q')).prod lam') {p | tanGauge p.1 + l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
  first | exact @GlobalTheory.OmegaSplit.omega_split | exact GlobalTheory.OmegaSplit.omega_split | (intros; apply GlobalTheory.OmegaSplit.omega_split <;> assumption)
