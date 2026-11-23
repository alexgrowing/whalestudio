import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinates
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
  ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
    ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first | exact @GlobalTheory.norm_isHomogeneous_poly_coords | exact GlobalTheory.norm_isHomogeneous_poly_coords | (intros; apply GlobalTheory.norm_isHomogeneous_poly_coords <;> assumption)
