import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormula
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_product_formula : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex | exact GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex <;> assumption)
