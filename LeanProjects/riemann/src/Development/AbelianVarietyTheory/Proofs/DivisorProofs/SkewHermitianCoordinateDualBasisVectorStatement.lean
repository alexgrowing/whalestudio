import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianCoordinate_dual_basisVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec <;> assumption)
