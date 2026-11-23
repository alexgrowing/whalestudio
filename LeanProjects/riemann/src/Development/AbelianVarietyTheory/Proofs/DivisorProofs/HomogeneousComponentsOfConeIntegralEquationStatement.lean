import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquation
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_components_of_cone_integral_equation : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 → ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.homogeneous_components_of_integral_equation | exact GlobalTheory.homogeneous_components_of_integral_equation | (intros; apply GlobalTheory.homogeneous_components_of_integral_equation <;> assumption)
