import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZero
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroForm_diagonal_bigCell_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  first | exact @GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | exact GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | (intros; apply GlobalTheory.LevelFormsReal.levelZero_im_eq_zero <;> assumption)
