import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyBinetColumnFrameProdDetPowEqSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : GlobalTheory.MinorFrame.Var ι d a → ℂ), GlobalTheory.MinorFrame.rsub (GlobalTheory.MinorFrame.frameMat x₀).conjTranspose (GlobalTheory.MinorFrame.detG a n) = ∑ T : GlobalTheory.MinorFrame.Tup ι a d n, star (MvPolynomial.eval x₀ (GlobalTheory.MinorFrame.prodMinors T)) • GlobalTheory.MinorFrame.prodMinors T := by
  first | exact @GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | exact GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | (intros; apply GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum <;> assumption)
