import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBound
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_cmConstant_add_logDerivative_le_squareTopBound : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x → Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ bTH D Cx large₂.sc.x large₂.sc.b := by
  first | exact @GlobalTheory.SizesArch.sizes | exact GlobalTheory.SizesArch.sizes | (intros; apply GlobalTheory.SizesArch.sizes <;> assumption)
