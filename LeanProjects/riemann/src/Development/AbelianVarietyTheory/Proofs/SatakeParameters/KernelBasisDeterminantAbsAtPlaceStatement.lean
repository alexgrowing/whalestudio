import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlace
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelBasis_determinant_abs_at_place : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  first | exact @GlobalTheory.SatakeUnitDeterminantBasis.detB | exact GlobalTheory.SatakeUnitDeterminantBasis.detB | (intros; apply GlobalTheory.SatakeUnitDeterminantBasis.detB <;> assumption)
