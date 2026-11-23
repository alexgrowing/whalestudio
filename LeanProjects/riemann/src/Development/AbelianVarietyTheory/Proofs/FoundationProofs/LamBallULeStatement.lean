import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_ballU_le_ofReal_pow : ∀ (p q : ℕ) (lam : Measure (lieU p q)), IsOmegaLeb lam → ∀ r : ℝ, 0 < r → lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  first | exact @GlobalTheory.CartanInt.LamBall.lam_ballU_le | exact GlobalTheory.CartanInt.LamBall.lam_ballU_le | (intros; apply GlobalTheory.CartanInt.LamBall.lam_ballU_le <;> assumption)
