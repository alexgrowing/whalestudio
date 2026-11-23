import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_polynomial_coefficients : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ), ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧ ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff | exact GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff | (intros; apply GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff <;> assumption)
