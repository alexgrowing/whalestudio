import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm → (∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) → ∀ x : EuclideanSpace ℝ l, f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec <;> assumption)
