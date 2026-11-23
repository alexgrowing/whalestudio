import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunction
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isQuotientMeasure_of_bruhat : ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T'] [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j → ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m'] [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, IsQuotientMeasure j m' m ν := by
  first | exact @GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | exact GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | (intros; apply GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction <;> assumption)
