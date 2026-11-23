import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicAlgebraicApproximation
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_algebraic_approximation : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (E : Type) [Field E] [IsAlgClosed E] [Algebra K E] (ι : E →+* ℂ_[p]), DenseRange ι → ∀ [Algebra K ℂ_[p]], ι.comp (algebraMap K E) = algebraMap K ℂ_[p] → ∀ (d m : ℕ) (t : Fin d → ℂ_[p]) (θ : ℂ_[p]) (P : Polynomial (MvPolynomial (Fin d) K)) (Δ : MvPolynomial (Fin d) K) (Q : Fin m → Polynomial (MvPolynomial (Fin d) K)) (η : ℝ), 0 < η → P.Monic → Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ P = 0 → MvPolynomial.aeval t Δ ≠ 0 → ∃ (t' : Fin d → E) (θ' : E), MvPolynomial.aeval t' Δ ≠ 0 ∧ Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' P = 0 ∧ ∀ j, ‖ι (Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j)) / ι (MvPolynomial.aeval t' Δ) - Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) / MvPolynomial.aeval t Δ‖ < η := by
  first | exact @GlobalTheory.exists_approx_point_of_denseRange | exact GlobalTheory.exists_approx_point_of_denseRange | (intros; apply GlobalTheory.exists_approx_point_of_denseRange <;> assumption)
