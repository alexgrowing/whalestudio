import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.GoodMetric

open Polynomial in
theorem chernPoly_zero' {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : chernPoly G v 0 = 1 := by
  rw [chernPoly, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

open Polynomial in
theorem chernPoly_above {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) (hk : Fintype.card r < k) : chernPoly G v k = 0 := by
  rw [chernPoly]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [← Matrix.reverse_charpoly]
  calc _ ≤ (Matrix.charpoly (-curvPoly G v)).natDegree := Polynomial.reverse_natDegree_le _
    _ = Fintype.card r := Matrix.charpoly_natDegree_eq_dim _
    _ < k := hk

theorem chernTop_unit : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  intro n ι m G v τ Q
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [chernTop, map_mul, map_sub, map_one, MvPolynomial.aeval_X, chernPoly_zero', sub_self, zero_mul,
      topCoeff, MvPolynomial.coeff_zero, mul_zero, Finset.sum_const_zero, Complex.zero_re]
  · have h := chernPoly_above (fun u => G u τ) v k (by simpa using hk)
    simp only [chernTop, map_mul, MvPolynomial.aeval_X, h, zero_mul,
      topCoeff, MvPolynomial.coeff_zero, mul_zero, Finset.sum_const_zero, Complex.zero_re]

end GlobalTheory.GoodMetric
