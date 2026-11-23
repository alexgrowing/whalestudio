import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinors
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellPoint_blockEnds_leadingMinors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  first | exact @GlobalTheory.Amp.PtMinor.blockEnds_minors | exact GlobalTheory.Amp.PtMinor.blockEnds_minors | (intros; apply GlobalTheory.Amp.PtMinor.blockEnds_minors <;> assumption)
