import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSq
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ballVol_succ_sq_eq_pow_mul_prod : ∀ (P Q : ℕ) (r : ℝ), 0 < r → ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) * ((volume : Measure (ℝ × Sp P Q)).prod (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))) {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  first | exact @GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | exact GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | (intros; apply GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq <;> assumption)
