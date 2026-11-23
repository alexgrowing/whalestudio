import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZero
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_primes_sum_squares_zero : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq | exact GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq | (intros; apply GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq <;> assumption)
