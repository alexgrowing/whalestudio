import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDetHermitianSumZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_det_hermitian_sum_zero : ∀ (D d : ℕ) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (H : α → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ) (K : β → Matrix (Fin d) (Fin d) ℂ), pol (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a + ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = 0 := by
  first | exact @GlobalTheory.FibreProj.DetPol.pol_det_perturb_eq_zero | exact GlobalTheory.FibreProj.DetPol.pol_det_perturb_eq_zero | (intros; apply GlobalTheory.FibreProj.DetPol.pol_det_perturb_eq_zero <;> assumption)
