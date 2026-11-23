import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPowerEqOfIntegralPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_power_eq_of_integral_points : ∀ {ι : Type} [Fintype ι] (n : ℕ) (Λ₁ Λ₂ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ a : ι → ℤ, Λ₁ ((∑ x, MvPolynomial.C (a x : ℝ) * MvPolynomial.X x) ^ n) = Λ₂ ((∑ x, MvPolynomial.C (a x : ℝ) * MvPolynomial.X x) ^ n)) → ∀ t : ι → ℝ, Λ₁ ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n) = Λ₂ ((∑ x, MvPolynomial.C (t x) * MvPolynomial.X x) ^ n) := by
  first | exact @GlobalTheory.linForm_pow_ext_of_int | exact GlobalTheory.linForm_pow_ext_of_int | (intros; apply GlobalTheory.linForm_pow_ext_of_int <;> assumption)
