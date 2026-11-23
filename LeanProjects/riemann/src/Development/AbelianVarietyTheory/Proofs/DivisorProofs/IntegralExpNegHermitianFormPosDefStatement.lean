import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpNegHermitianFormPosDef
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_exp_neg_hermitian_form_posDef : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef → Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧ ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) = Real.pi ^ n / H.det.re := by
  first | exact @GlobalTheory.GaussHerm.integral_exp_neg_herm | exact GlobalTheory.GaussHerm.integral_exp_neg_herm | (intros; apply GlobalTheory.GaussHerm.integral_exp_neg_herm <;> assumption)
