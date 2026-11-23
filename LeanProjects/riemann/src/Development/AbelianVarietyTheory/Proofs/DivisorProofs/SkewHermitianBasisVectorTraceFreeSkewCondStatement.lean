import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCond
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec <;> assumption)
