import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNorms
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralForm_parameter_of_discreteNorms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  first | exact @GlobalTheory.MBLow.exists_form_of_discrete_norms | exact GlobalTheory.MBLow.exists_form_of_discrete_norms | (intros; apply GlobalTheory.MBLow.exists_form_of_discrete_norms <;> assumption)
