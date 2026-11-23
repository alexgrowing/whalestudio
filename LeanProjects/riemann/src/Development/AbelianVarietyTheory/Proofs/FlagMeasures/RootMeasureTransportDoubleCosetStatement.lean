import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootMeasure_transport_doubleCoset : ∀ (D : D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : Point ℂ (D.R.rS + 1)) (g a a' : MatKR D.R.k D.R.rS) (μ : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → g ∈ UH (Hpk D.R.k D.R.rS) → a ∈ Sset D.R.k D.R.rS z → a' ∈ Sset D.R.k D.R.rS z' → IsRootMeasR D z z' p g μ → IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  first | exact @GlobalTheory.Amp.RootMove.rootMeas_move | exact GlobalTheory.Amp.RootMove.rootMeas_move | (intros; apply GlobalTheory.Amp.RootMove.rootMeas_move <;> assumption)
